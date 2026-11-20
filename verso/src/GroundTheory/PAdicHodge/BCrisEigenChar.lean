import Mathlib
import GroundTheory.PAdicHodge.BCrisEigenFrob
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace EigenChar

open GroundTheory.LocalField EigenWitt

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
The claim follows from `(algebraMap ℚ_[p] ℂ_[p]).injective`.
-/
theorem algebraMap_padic_cp_injective : Function.Injective (algebraMap ℚ_[p] ℂ_[p]) :=
  (algebraMap ℚ_[p] ℂ_[p]).injective

/- English proof (translation)
The claim follows from `AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap' ℂ_[p])`.
-/
theorem isometry_algebraMap_padic_cp : Isometry (algebraMap ℚ_[p] ℂ_[p]) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_algebraMap' ℂ_[p])

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
The claim follows from `algebraMap_padic_cp_injective (mul_right_cancel₀ hx h)`.
-/
theorem eq_of_mul_eq {x : ℂ_[p]} (hx : x ≠ 0) {q q' : ℚ_[p]}
    (h : algebraMap ℚ_[p] ℂ_[p] q * x = algebraMap ℚ_[p] ℂ_[p] q' * x) : q = q' :=
  algebraMap_padic_cp_injective (mul_right_cancel₀ hx h)

/- English proof (translation)
Use `choose q hq using h`. Set `ψ₀ : Gal(PadicAlgCl p/K) →* ℚ_[p]` to `{ toFun := q map_one' := eq_of_mul_eq hx (by rw [← hq, one_smul, map_one, one_mul]) map_mul' := fun σ τ => eq_of_mul_eq hx (by`. Rewrite using `[← hq, mul_smul, hq τ, smul_mul', gal_smul_algebraMap, hq σ, map_mul]`. Use the proof step `ring) }`. Establish `hcont₀ : Continuous ψ₀`.

Rewrite using `[isometry_algebraMap_padic_cp.isEmbedding.continuous_iff]`. Establish `e : (algebraMap ℚ_[p] ℂ_[p]) ∘ ψ₀ = fun σ => (σ • x) * x⁻¹`. Use function extensionality and compare the values at `σ`. Simplify using `only [Function.comp_apply]`. Express the relevant statement in the definitionally equal form `algebraMap ℚ_[p] ℂ_[p] (q σ) = _`.

Rewrite using `[hq σ, mul_assoc, mul_inv_cancel₀ hx, mul_one]`. Rewrite using `[e]`. Conclude with `(continuous_id.smul continuous_const).mul continuous_const`. Use `⟨ψ₀.toHomUnits, ?_, fun σ => hq σ⟩` and prove the remaining obligations. Rewrite using `[Units.continuous_iff]`.

Use `⟨hcont₀, ?_⟩` and prove the remaining obligations. Establish `e : (fun σ => (((ψ₀.toHomUnits σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) = ψ₀ ∘ fun σ => σ⁻¹`. Use function extensionality and compare the values at `σ`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `hcont₀.comp continuous_inv`.
-/
theorem exists_eigenChar {x : ℂ_[p]} (hx : x ≠ 0)
    (h : ∀ σ : Gal(PadicAlgCl p/K), ∃ q : ℚ_[p], σ • x = algebraMap ℚ_[p] ℂ_[p] q * x) :
    ∃ ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ, Continuous ψ ∧
      ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x := by
  choose q hq using h
  let ψ₀ : Gal(PadicAlgCl p/K) →* ℚ_[p] :=
    { toFun := q
      map_one' := eq_of_mul_eq hx (by rw [← hq, one_smul, map_one, one_mul])
      map_mul' := fun σ τ => eq_of_mul_eq hx (by
        rw [← hq, mul_smul, hq τ, smul_mul', gal_smul_algebraMap, hq σ, map_mul]
        ring) }
  have hcont₀ : Continuous ψ₀ := by
    rw [isometry_algebraMap_padic_cp.isEmbedding.continuous_iff]
    have e : (algebraMap ℚ_[p] ℂ_[p]) ∘ ψ₀ = fun σ => (σ • x) * x⁻¹ := by
      funext σ
      simp only [Function.comp_apply]
      change algebraMap ℚ_[p] ℂ_[p] (q σ) = _
      rw [hq σ, mul_assoc, mul_inv_cancel₀ hx, mul_one]
    rw [e]
    exact (continuous_id.smul continuous_const).mul continuous_const
  refine ⟨ψ₀.toHomUnits, ?_, fun σ => hq σ⟩
  rw [Units.continuous_iff]
  refine ⟨hcont₀, ?_⟩
  have e : (fun σ => (((ψ₀.toHomUnits σ)⁻¹ : ℚ_[p]ˣ) : ℚ_[p])) = ψ₀ ∘ fun σ => σ⁻¹ := by
    funext σ
    rw [← map_inv]
    rfl
  rw [e]
  exact hcont₀.comp continuous_inv

/- English proof (translation)
Establish `h1` using `norm_smul_gal σ x`. Rewrite `h1` using `[h, norm_mul, norm_algebraMap']`. Conclude with `mul_right_cancel₀ (norm_ne_zero_iff.2 hx) (h1.trans (one_mul _).symm)`.
-/
theorem norm_eigen_eq_one {x : ℂ_[p]} (hx : x ≠ 0) {σ : Gal(PadicAlgCl p/K)} {q : ℚ_[p]}
    (h : σ • x = algebraMap ℚ_[p] ℂ_[p] q * x) : ‖q‖ = 1 := by
  have h1 := norm_smul_gal σ x
  rw [h, norm_mul, norm_algebraMap'] at h1
  exact mul_right_cancel₀ (norm_ne_zero_iff.2 hx) (h1.trans (one_mul _).symm)

def galRes {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L) :
    Gal(PadicAlgCl p/L) →* Gal(PadicAlgCl p/K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun k => σ.commutes ⟨(k : PadicAlgCl p), hKL k.2⟩)
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem galRes_apply {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L)
    (σ : Gal(PadicAlgCl p/L)) (y : PadicAlgCl p) : galRes hKL σ y = σ y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem galRes_smul {L : IntermediateField ℚ_[p] (PadicAlgCl p)} (hKL : K ≤ L)
    (σ : Gal(PadicAlgCl p/L)) (x : ℂ_[p]) : galRes hKL σ • x = σ • x := rfl

/- English proof (translation)
Use `set F := ψ '' S \ {1} with hF`. Establish `hFc : IsClosed F` using `(hfin.subset Set.sdiff_subset).isClosed`. Establish `hO : ψ ⁻¹' Fᶜ ∈ nhds (1 : Gal(PadicAlgCl p/K))`. Use `(hFc.isOpen_compl.preimage hψ).mem_nhds ?_` and prove the remaining obligations. Simplify using `[hF]`.

Take `⟨E, hE, hsub⟩` from `(krullTopology_mem_nhds_one_iff K (PadicAlgCl p) _).1 hO`. Use `⟨E, hE, fun σ hσ hS => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `hsub hσ ⟨⟨σ, hS, rfl⟩, hne⟩`.
-/
theorem exists_fixingSubgroup_of_finite_image (ψ : Gal(PadicAlgCl p/K) →* ℚ_[p]ˣ) (hψ : Continuous ψ)
    (S : Set Gal(PadicAlgCl p/K)) (hfin : (ψ '' S).Finite) :
    ∃ E : IntermediateField K (PadicAlgCl p), FiniteDimensional K E ∧
      ∀ σ ∈ E.fixingSubgroup, σ ∈ S → ψ σ = 1 := by
  set F := ψ '' S \ {1} with hF
  have hFc : IsClosed F := (hfin.subset Set.sdiff_subset).isClosed
  have hO : ψ ⁻¹' Fᶜ ∈ nhds (1 : Gal(PadicAlgCl p/K)) := by
    refine (hFc.isOpen_compl.preimage hψ).mem_nhds ?_
    simp [hF]
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K (PadicAlgCl p) _).1 hO
  refine ⟨E, hE, fun σ hσ hS => ?_⟩
  by_contra hne
  exact hsub hσ ⟨⟨σ, hS, rfl⟩, hne⟩

/- English proof (translation)
Establish `hker : σ ∈ (maximalUnramifiedExtension L (PadicAlgCl p)).fixingSubgroup`. Rewrite using `[← ker_unramifiedDegree]`. Conclude with `hσ`. Establish `hroot : ∀ ζ ∈ primeToPRoots p, σ ζ = ζ`. Introduce and unpack `ζ ⟨m, hm, hcop, hζ⟩`.

Use `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hker ζ (unramifiedRoots_subset_maximalUnramifiedExtension (mem_unramifiedRoots_iff.2 ⟨m, ?_, hζ⟩))` and prove the remaining obligations. Introduce `h0`. Rewrite `h0` using `[CharP.cast_eq_zero_iff _ p]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop.symm h0`. Introduce `u hu`.

Proceed by induction on `hu using IntermediateField.adjoin_induction with`. Consider the case `mem x hx => exact hroot x hx`. Consider the case `algebraMap q`. Conclude with `σ.commutes (algebraMap ℚ_[p] L q)`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`.

Consider the case `inv x _ hx => rw [map_inv₀, hx]`. Consider the case `mul x y _ _ hx hy => rw [map_mul, hx, hy]`.
-/
theorem mem_inertia_of_degree {L : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] L]
    {σ : Gal(PadicAlgCl p/L)} (hσ : unramifiedDegree L (PadicAlgCl p) σ = 1) :
    ∀ u ∈ unramifiedClosure p, σ u = u := by
  have hker : σ ∈ (maximalUnramifiedExtension L (PadicAlgCl p)).fixingSubgroup := by
    rw [← ker_unramifiedDegree]
    exact hσ
  have hroot : ∀ ζ ∈ primeToPRoots p, σ ζ = ζ := by
    rintro ζ ⟨m, hm, hcop, hζ⟩
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).1 hker ζ
      (unramifiedRoots_subset_maximalUnramifiedExtension (mem_unramifiedRoots_iff.2 ⟨m, ?_, hζ⟩))
    intro h0
    rw [CharP.cast_eq_zero_iff _ p] at h0
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 hcop.symm h0
  intro u hu
  induction hu using IntermediateField.adjoin_induction with
  | mem x hx => exact hroot x hx
  | algebraMap q =>
    exact σ.commutes (algebraMap ℚ_[p] L q)
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/- English proof (translation)
Use `isSepClosure_padicAlgCl (L := L)` as an intermediate fact. Take `⟨σ₀, hσ₀⟩` from `unramifiedDegree_surjective (K := L) (Ω := PadicAlgCl p) (Multiplicative.ofAdd 1)`. Establish `hw : ‖((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1` using `norm_eigen_eq_one hx (hψx σ₀)`. Use `set w : ℤ_[p]ˣ := PadicInt.mkUnits hw with hwdef`. Establish `hwcoe : ((w : ℤ_[p]) : ℚ_[p]) = ((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p])` using `rfl`.

Take `⟨f, hf, hq⟩` from `exists_card_residueField_eq_pow (L := L)`. Take `⟨b, hb, hbσ⟩` from `exists_unit_aInf_eigen (K := L) w`. Use `set cA := wittToAInf (b : WittVector p (Fpbar p)) with hcA`. Establish `hcu : IsUnit cA` using `b.isUnit.map _`. Use `set θ := WittVector.fontaineTheta (normInteger ℂ_[p]) p`.

Use `set xc : ℂ_[p] := ((θ cA : normInteger ℂ_[p]) : ℂ_[p]) with hxcdef`. Establish `hxc : xc ≠ 0`. Establish `h1 : θ cA ≠ 0` using `(hcu.map θ).ne_zero`. Conclude with `fun h => h1 (Subtype.ext h)`. Use `choose z hz using hbσ`.

Establish `hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[p] ℂ_[p] (z σ) * xc` using `fun σ => by`. Rewrite using `[hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul, fontaineTheta_padicIntToWitt]`. Establish `hz0 : ∀ σ, (z σ : ℚ_[p]) ≠ 0` using `fun σ h => by`. Use `norm_eigen_eq_one hxc (hxcσ σ)` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`.

Conclude with `zero_ne_one this`. Use `set X := x ^ f * xc⁻¹ with hXdef`. Establish `hX : X ≠ 0` using `mul_ne_zero (pow_ne_zero _ hx) (inv_ne_zero hxc)`. Establish `hXσ : ∀ σ, σ • X = algebraMap ℚ_[p] ℂ_[p] (((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹) * X` using `fun σ => by`. Rewrite using `[hXdef, ← galCp_apply, map_mul, map_pow, map_inv₀, galCp_apply, galCp_apply, hψx σ, hxcσ σ, map_mul, map_pow, map_inv₀]`.

Establish `hz' : algebraMap ℚ_[p] ℂ_[p] (z σ : ℚ_[p]) ≠ 0` using `(map_ne_zero_iff _ algebraMap_padic_cp_injective).2 (hz0 σ)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨ρ, hρc, hρ⟩` from `exists_eigenChar hX (fun σ => ⟨_, hXσ σ⟩)`. Establish `hρeq : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹` using `fun σ => eq_of_mul_eq hX ((hρ σ).symm.trans (hXσ σ))`.

Establish `hz₀ : (z σ₀ : ℚ_[p]) = ((w : ℤ_[p]) : ℚ_[p]) ^ f`. Establish `h1` using `gal_smul_twist_of_degree_one hb hq hσ₀`. Rewrite `h1` using `[← hcA, hz σ₀]`. Establish `h2` using `hcu.mul_left_inj.1 h1`. Establish `h3` using `congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) h2`.

Simplify using `only [θ, fontaineTheta_padicIntToWitt] at h3`. Rewrite using `[← PadicInt.coe_pow]`. Conclude with `algebraMap_padic_cp_injective h3`. Establish `hzI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → (z σ : ℚ_[p]) = 1` using `fun σ hσ => by`. Establish `h1` using `gal_smul_twist_of_inertia (b : WittVector p (Fpbar p)) hσ`.

Rewrite `h1` using `[← hcA, hz σ]`. Establish `h2 : IsPerfectoidField.padicIntToWitt p (z σ) * cA = IsPerfectoidField.padicIntToWitt p 1 * cA`. Rewrite using `[h1, map_one, one_mul]`. Establish `h3` using `congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) (hcu.mul_left_inj.1 h2)`. Simplify using `only [θ, fontaineTheta_padicIntToWitt] at h3`.

Use `algebraMap_padic_cp_injective h3` as an intermediate fact. Rewrite using `[this, PadicInt.coe_one]`. Set `ρC : Gal(PadicAlgCl p/L) →* ℂ_[p]` to `(algebraMap ℚ_[p] ℂ_[p]).toMonoidHom.comp ((Units.coeHom ℚ_[p]).comp ρ)`. Establish `hρC : Continuous ρC` using `isometry_algebraMap_padic_cp.continuous.comp (Units.continuous_val.comp hρc)`. Establish `hρ1 : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 → ρC σ = 1` using `fun σ h => by`.

Express the relevant statement in the definitionally equal form `algebraMap ℚ_[p] ℂ_[p] ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1`. Rewrite using `[h, map_one]`. Establish `hall` using `eq_one_of_degree_one ρC hρC hσ₀ (hρ1 σ₀ (by rw [hρeq, hz₀, hwcoe, mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _))])) (fun σ hσ => hρ1 σ (by rw [hρeq, hzI σ hσ, hI σ hσ, Units.val_one, one_pow, inv_one, mul_one]))`. Use `⟨f, hf, hcu.unit, fun σ => ⟨z σ, ?_, hz σ⟩⟩` and prove the remaining obligations. Establish `h1 : ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1` using `algebraMap_padic_cp_injective (by`.

Rewrite using `[map_one]`. Conclude with `hall σ)`. Rewrite `h1` using `[hρeq]`. Conclude with `(mul_inv_eq_one₀ (hz0 σ)).1 h1 |>.symm`.
-/
theorem exists_twist_of_unramified {L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] L] {x : ℂ_[p]} (hx : x ≠ 0) (ψ : Gal(PadicAlgCl p/L) →* ℚ_[p]ˣ)
    (hψx : ∀ σ, σ • x = algebraMap ℚ_[p] ℂ_[p] (ψ σ) * x)
    (hI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → ψ σ = 1) :
    ∃ f : ℕ, 0 < f ∧ ∃ c : (AInf ℂ_[p] p)ˣ, ∀ σ : Gal(PadicAlgCl p/L), ∃ z : ℤ_[p],
      (z : ℚ_[p]) = ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f ∧
      σ • (c : AInf ℂ_[p] p) = IsPerfectoidField.padicIntToWitt p z * (c : AInf ℂ_[p] p) := by
  have := isSepClosure_padicAlgCl (L := L)
  obtain ⟨σ₀, hσ₀⟩ := unramifiedDegree_surjective (K := L) (Ω := PadicAlgCl p)
    (Multiplicative.ofAdd 1)
  have hw : ‖((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := norm_eigen_eq_one hx (hψx σ₀)
  set w : ℤ_[p]ˣ := PadicInt.mkUnits hw with hwdef
  have hwcoe : ((w : ℤ_[p]) : ℚ_[p]) = ((ψ σ₀ : ℚ_[p]ˣ) : ℚ_[p]) := rfl
  obtain ⟨f, hf, hq⟩ := exists_card_residueField_eq_pow (L := L)
  obtain ⟨b, hb, hbσ⟩ := exists_unit_aInf_eigen (K := L) w
  set cA := wittToAInf (b : WittVector p (Fpbar p)) with hcA
  have hcu : IsUnit cA := b.isUnit.map _
  set θ := WittVector.fontaineTheta (normInteger ℂ_[p]) p
  set xc : ℂ_[p] := ((θ cA : normInteger ℂ_[p]) : ℂ_[p]) with hxcdef
  have hxc : xc ≠ 0 := by
    have h1 : θ cA ≠ 0 := (hcu.map θ).ne_zero
    exact fun h => h1 (Subtype.ext h)
  choose z hz using hbσ
  have hxcσ : ∀ σ, σ • xc = algebraMap ℚ_[p] ℂ_[p] (z σ) * xc := fun σ => by
    rw [hxcdef, ← AInf.fontaineTheta_gal_smul, hz σ, map_mul, Subring.coe_mul,
      fontaineTheta_padicIntToWitt]
  have hz0 : ∀ σ, (z σ : ℚ_[p]) ≠ 0 := fun σ h => by
    have := norm_eigen_eq_one hxc (hxcσ σ)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set X := x ^ f * xc⁻¹ with hXdef
  have hX : X ≠ 0 := mul_ne_zero (pow_ne_zero _ hx) (inv_ne_zero hxc)
  have hXσ : ∀ σ, σ • X = algebraMap ℚ_[p] ℂ_[p]
      (((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹) * X := fun σ => by
    rw [hXdef, ← galCp_apply, map_mul, map_pow, map_inv₀, galCp_apply, galCp_apply, hψx σ, hxcσ σ,
      map_mul, map_pow, map_inv₀]
    have hz' : algebraMap ℚ_[p] ℂ_[p] (z σ : ℚ_[p]) ≠ 0 :=
      (map_ne_zero_iff _ algebraMap_padic_cp_injective).2 (hz0 σ)
    field_simp
    ring
  obtain ⟨ρ, hρc, hρ⟩ := exists_eigenChar hX (fun σ => ⟨_, hXσ σ⟩)
  have hρeq : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) =
      ((ψ σ : ℚ_[p]ˣ) : ℚ_[p]) ^ f * (z σ : ℚ_[p])⁻¹ := fun σ =>
    eq_of_mul_eq hX ((hρ σ).symm.trans (hXσ σ))
  have hz₀ : (z σ₀ : ℚ_[p]) = ((w : ℤ_[p]) : ℚ_[p]) ^ f := by
    have h1 := gal_smul_twist_of_degree_one hb hq hσ₀
    rw [← hcA, hz σ₀] at h1
    have h2 := hcu.mul_left_inj.1 h1
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) h2
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    rw [← PadicInt.coe_pow]
    exact algebraMap_padic_cp_injective h3
  have hzI : ∀ σ, unramifiedDegree L (PadicAlgCl p) σ = 1 → (z σ : ℚ_[p]) = 1 := fun σ hσ => by
    have h1 := gal_smul_twist_of_inertia (b : WittVector p (Fpbar p)) hσ
    rw [← hcA, hz σ] at h1
    have h2 : IsPerfectoidField.padicIntToWitt p (z σ) * cA = IsPerfectoidField.padicIntToWitt p 1 * cA := by
      rw [h1, map_one, one_mul]
    have h3 := congrArg (fun y => ((θ y : normInteger ℂ_[p]) : ℂ_[p])) (hcu.mul_left_inj.1 h2)
    simp only [θ, fontaineTheta_padicIntToWitt] at h3
    have := algebraMap_padic_cp_injective h3
    rw [this, PadicInt.coe_one]
  let ρC : Gal(PadicAlgCl p/L) →* ℂ_[p] :=
    (algebraMap ℚ_[p] ℂ_[p]).toMonoidHom.comp ((Units.coeHom ℚ_[p]).comp ρ)
  have hρC : Continuous ρC :=
    isometry_algebraMap_padic_cp.continuous.comp (Units.continuous_val.comp hρc)
  have hρ1 : ∀ σ, ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 → ρC σ = 1 := fun σ h => by
    change algebraMap ℚ_[p] ℂ_[p] ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1
    rw [h, map_one]
  have hall := eq_one_of_degree_one ρC hρC hσ₀
    (hρ1 σ₀ (by rw [hρeq, hz₀, hwcoe, mul_inv_cancel₀ (pow_ne_zero _ (Units.ne_zero _))]))
    (fun σ hσ => hρ1 σ (by rw [hρeq, hzI σ hσ, hI σ hσ, Units.val_one, one_pow, inv_one, mul_one]))
  refine ⟨f, hf, hcu.unit, fun σ => ⟨z σ, ?_, hz σ⟩⟩
  have h1 : ((ρ σ : ℚ_[p]ˣ) : ℚ_[p]) = 1 := algebraMap_padic_cp_injective (by
    rw [map_one]
    exact hall σ)
  rw [hρeq] at h1
  exact (mul_inv_eq_one₀ (hz0 σ)).1 h1 |>.symm

end EigenChar

end GroundTheory.PAdicHodge
