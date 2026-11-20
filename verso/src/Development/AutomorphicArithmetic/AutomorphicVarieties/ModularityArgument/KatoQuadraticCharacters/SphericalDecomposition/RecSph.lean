import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnlSph
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.RcChars
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaFixesRootsOfUnityPrimeToResidueChar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfUnr

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af
open UpperTheory.V UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `GlobalTheory.PrinTwo.NoFix.exists_unif k`. Conclude with `⟨_, eq_unrChar h hϖ⟩`.
-/
private theorem exists_unr {ξ : kˣ →* ℂˣ} (h : IsUnram ξ) : ∃ a : ℂˣ, ξ = unrChar k a := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  exact ⟨_, eq_unrChar h hϖ⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `GlobalTheory.PrinTwo.NoFix.exists_unif k`. Establish `hU : IsUnram (unrChar k a * absPow k 1)` using `fun u hu => by`. Rewrite using `[MonoidHom.mul_apply, isUnram_unrChar k a u hu, isUnram_absPow k 1 u hu, one_mul]`. Rewrite using `[eq_unrChar hU hϖ]`. Use `congr 1`.

Use `Units.ext ?_` and prove the remaining obligations. Simplify using `only [MonoidHom.mul_apply, Units.val_mul]`. Rewrite using `[unrChar_uniformizer k a hϖ, val_absPow, Complex.cpow_one, h]`. Establish `hn : nabs k ϖ = (resCard k : ℝ)⁻¹`. Rewrite using `[GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]`.

Simplify using the standard rewrite rules. Establish `hq : (resCard k : ℂ) ≠ 0`. Establish `: (1 : ℝ) < resCard k` using `by exact_mod_cast one_lt_resCard (k := k)`. Conclude with `(by positivity : (resCard k : ℝ) ≠ 0)` after adjusting the coercions. Rewrite using `[hn]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
private theorem unr_eq {a b : ℂˣ} (h : (a : ℂ) = (resCard k : ℂ) * b) : unrChar k b = unrChar k a * absPow k 1 := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have hU : IsUnram (unrChar k a * absPow k 1) := fun u hu => by
    rw [MonoidHom.mul_apply, isUnram_unrChar k a u hu, isUnram_absPow k 1 u hu, one_mul]
  rw [eq_unrChar hU hϖ]
  congr 1
  refine Units.ext ?_
  simp only [MonoidHom.mul_apply, Units.val_mul]
  rw [unrChar_uniformizer k a hϖ, val_absPow, Complex.cpow_one, h]
  have hn : nabs k ϖ = (resCard k : ℝ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one hϖ]; simp
  have hq : (resCard k : ℂ) ≠ 0 := by
    have : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard (k := k)
    exact_mod_cast (by positivity : (resCard k : ℝ) ≠ 0)
  rw [hn]
  push_cast
  field_simp

end Loc

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Take `⟨χ, b, hχ, e, hN, hb⟩` from `hL`. Establish `h1 : ((1 : ℕ) : 𝓞 E) ∉ w.asIdeal`. Rewrite using `[Nat.cast_one]`. Conclude with `fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`. Rewrite using `[← e, WD.unr_mk]`.

Use `⟨hN, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[hb s]`. Simplify using `[fun i => hχ i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char E Ω w A h 1 h1 s s.2), Module.End.one_eq_id]`.
-/
private theorem unr_of_level {n : ℕ} {x : WD h} (hL : IsLevelWD 1 n x) : x.unr := by
  obtain ⟨χ, b, hχ, e, hN, hb⟩ := hL
  have h1 : ((1 : ℕ) : 𝓞 E) ∉ w.asIdeal := by
    rw [Nat.cast_one]
    exact fun h1 => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  rw [← e, WD.unr_mk]
  refine ⟨hN, fun s => ?_⟩
  rw [hb s]
  simp [fun i => hχ i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char E Ω w A h 1 h1 s s.2), Module.End.one_eq_id]

/- English proof (translation)
Take `⟨m, b, rfl⟩` from `x.exists_rep`. Rewrite `hu` using `[WD.unr_mk]`. Rewrite `hz` using `[WD.charPol_mk, hu.2 t, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]`. Take `⟨v, hv⟩` from `hz.exists_hasEigenvector`. Establish `h3` using `hv.apply_eq_smul`.

Conclude with `smul_left_injective ℂ hv.2 (by simpa using h3.symm)`.
-/
private theorem eq_one_of_root {x : WD h} (hu : x.unr) (t : Ine (F := E) A) {z : ℂ}
    (hz : (x.charPol (ineIncl h t)).IsRoot z) : z = 1 := by
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.unr_mk] at hu
  rw [WD.charPol_mk, hu.2 t, ← Module.End.hasEigenvalue_iff_isRoot_charpoly] at hz
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have h3 := hv.apply_eq_smul
  exact smul_left_injective ℂ hv.2 (by simpa using h3.symm)

end WD

end UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity

open UpperTheory.V.Z.Kato.WeilSphericalRecords.SphericalReciprocity in
/- English proof (translation)
Introduce `_ E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ hP hlev`. Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Establish `hxu : (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).unr`. Establish `h0` using `unr_of_level hlev`. Rewrite `h0` using `[algNorm, L.nu, WD.unr_tw]`. Then use the resulting hypothesis.

Take `⟨ξ, hξ, hs, hu⟩` from `GlobalTheory.RoadU.plainTor_exists_chars _ _ hP`. Establish `hun : ∀ i, IsUnram (ξ i)` using `fun i u hu1 => by`. Take `⟨g, rfl⟩` from `ha.surj u`. Establish `h0 : deg g = 0`. Establish `h1` using `ha.ord_eq g`.

Rewrite `h1` using `[ord_eq_zero_iff.2 hu1]`. Use linear arithmetic over natural numbers and integers. Establish `hr : ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol (ineIncl h ⟨g, deg_eq_zero_iff.1 h0⟩)).IsRoot ((ξ i (a g) : ℂˣ) : ℂ)`. Rewrite using `[charPol_of_chars L _ ξ hξ hs]`. Use `IsRoot.dvd ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))` and prove the remaining obligations.

Simplify using `only [eval_sub, eval_X, eval_C, IsRoot.def]`. Conclude with `sub_self _`. Conclude with `Units.ext (eq_one_of_root hxu _ hr)`. Use `choose α hα using fun i => exists_unr (hun i)`. Take `rfl : ξ = fun i => GlobalTheory.SmGL.unrChar _ (α i)` from `funext hα`.

Establish `hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars _ hξ)` using `hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm`. Take `⟨-, hq⟩` from `(UpperTheory.Gal.LocD.ofSupport_holds _ n σ.V σ.ρ _ hξ).1 hs'`. Establish `hN : (resCard (w.adicCompletion E) : ℂ) = (Ideal.absNorm w.asIdeal : ℂ)`. Use `GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm E w` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `hne : ∀ i j, (α i : ℂ) ≠ (Ideal.absNorm w.asIdeal : ℂ) * α j` using `fun i j e => by`. Establish `hm : ∀ l, IrrGL.ofChar (GlobalTheory.SmGL.unrChar _ (α l)) (hξ l) ∈ GlobalTheory.RoadU.chars _ hξ` using `fun l => Multiset.mem_map_of_mem (fun i => IrrGL.ofChar (GlobalTheory.SmGL.unrChar _ (α i)) (hξ i)) (Finset.mem_univ l)`. Use `hu _ (hm j) _ (hm i) ?_` and prove the remaining obligations. Simplify using `only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]`. Conclude with `unr_eq (by rw [hN]; exact e)`.

Establish `hsph` using `UpperTheory.ConvolutionTheory.Sph.unlSph E n w σ α hne hq`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).1 hsph`. Rewrite `hv` using `[GlobalTheory.SmGL.SphCompletion.KO_completion w n]`. Conclude with `⟨v, hv0, GlobalTheory.LGrp.mem_fixed.1 hv⟩`.
-/
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.recSph :
    Af.Hypotheses₂ → RecSph := by
  intro _ E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ hP hlev
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hxu : (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).unr := by
    have h0 := unr_of_level hlev
    rwa [algNorm, L.nu, WD.unr_tw] at h0
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hun : ∀ i, IsUnram (ξ i) := fun i u hu1 => by
    obtain ⟨g, rfl⟩ := ha.surj u
    have h0 : deg g = 0 := by
      have h1 := ha.ord_eq g
      rw [ord_eq_zero_iff.2 hu1] at h1
      omega
    have hr : ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol (ineIncl h ⟨g, deg_eq_zero_iff.1 h0⟩)).IsRoot
        ((ξ i (a g) : ℂˣ) : ℂ) := by
      rw [charPol_of_chars L _ ξ hξ hs]
      refine IsRoot.dvd ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
      simp only [eval_sub, eval_X, eval_C, IsRoot.def]
      exact sub_self _
    exact Units.ext (eq_one_of_root hxu _ hr)
  choose α hα using fun i => exists_unr (hun i)
  obtain rfl : ξ = fun i => GlobalTheory.SmGL.unrChar _ (α i) := funext hα
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars _ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  obtain ⟨-, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds _ n σ.V σ.ρ _ hξ).1 hs'
  have hN : (resCard (w.adicCompletion E) : ℂ) = (Ideal.absNorm w.asIdeal : ℂ) := by
    have := GlobalTheory.CompanionTheory.ResCardAbsNorm.resCard_completion_eq_absNorm E w
    exact_mod_cast this
  have hne : ∀ i j, (α i : ℂ) ≠ (Ideal.absNorm w.asIdeal : ℂ) * α j := fun i j e => by
    have hm : ∀ l, IrrGL.ofChar (GlobalTheory.SmGL.unrChar _ (α l)) (hξ l) ∈ GlobalTheory.RoadU.chars _ hξ := fun l =>
      Multiset.mem_map_of_mem (fun i => IrrGL.ofChar (GlobalTheory.SmGL.unrChar _ (α i)) (hξ i)) (Finset.mem_univ l)
    refine hu _ (hm j) _ (hm i) ?_
    simp only [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]
    exact unr_eq (by rw [hN]; exact e)
  have hsph := UpperTheory.ConvolutionTheory.Sph.unlSph E n w σ α hne hq
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hsph
  rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n] at hv
  exact ⟨v, hv0, GlobalTheory.LGrp.mem_fixed.1 hv⟩
