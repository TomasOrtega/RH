import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IrrWeilAbs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Set `S : Set (Module.End ℂ (Fin n → ℂ))` to `Set.range fun τ : Ine (F := E) A => a.ρ (ineIncl h τ)`. Use `haveI : Finite S := a.smooth.finite_range.to_subtype`. Establish `conj_mem : ∀ (k : ℕ), ∀ s ∈ S, a.ρ (φ ^ k) * s * a.ρ ((φ ^ k)⁻¹) ∈ S`. Introduce and unpack `k _ ⟨τ, rfl⟩`. Establish `h0 : deg (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) = 0` using `by simp`.

Use `⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_mul]`. Conclude with `congrArg a.ρ (Subtype.ext rfl)`. Set `g : ℕ → (S → S)` to `fun k s => ⟨_, conj_mem k s.1 s.2⟩`. Take `⟨k1, k2, hne, heq⟩` from `Finite.exists_ne_map_eq_of_infinite g`.

Choose the witnesses or unpack the hypotheses as in `⟨k, m, hm, hkm⟩ : ∃ k m : ℕ, 0 < m ∧ g k = g (k + m) := by`. Break down `lt_or_gt_of_ne hne with hl | hl` into its components or cases. Conclude with `⟨k1, k2 - k1, by omega, by rw [show k1 + (k2 - k1) = k2 by omega]; exact heq⟩`. Conclude with `⟨k2, k1 - k2, by omega, by rw [show k2 + (k1 - k2) = k1 by omega]; exact heq.symm⟩`. Establish `comm_ine : ∀ τ : Ine (F` using `E) A, a.ρ (φ ^ m) * a.ρ (ineIncl h τ) = a.ρ (ineIncl h τ) * a.ρ (φ ^ m) := by`.

Introduce `τ`. Establish `e1 : a.ρ (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) = a.ρ (φ ^ (k + m) * ineIncl h τ * (φ ^ (k + m))⁻¹)`. Use `congrArg Subtype.val (congrFun hkm ⟨_, τ, rfl⟩)` as an intermediate fact. Rewrite using `[map_mul, map_mul, map_mul, map_mul]`. Conclude with `this`.

Establish `e2` using `congrArg (fun X => a.ρ ((φ ^ k)⁻¹) * X * a.ρ (φ ^ k * φ ^ m)) e1`. Simplify using `only [← map_mul] at e2`. Rewrite using `[← map_mul, ← map_mul]`. Apply the tactic sequence `convert e2.symm using 2 <;> group`. Use `⟨m, hm, fun σ => ?_⟩` and prove the remaining obligations.

Take `⟨τ, hτ⟩` from `exists_eq_zpow_mul hφ σ`. Establish `hc : φ ^ m * φ ^ deg σ = φ ^ deg σ * φ ^ m` using `((Commute.refl φ).pow_left m).zpow_right (deg σ)`. Rewrite using `[hτ, map_mul, ← mul_assoc, ← map_mul, hc, map_mul, mul_assoc, comm_ine, ← mul_assoc]`.
-/
theorem exists_pow_central {n : ℕ} (a : WDRep h (Fin n → ℂ)) {φ : Weil h} (hφ : deg φ = 1) :
    ∃ m : ℕ, 0 < m ∧ ∀ σ : Weil h, a.ρ (φ ^ m) * a.ρ σ = a.ρ σ * a.ρ (φ ^ m) := by
  classical
  let S : Set (Module.End ℂ (Fin n → ℂ)) := Set.range fun τ : Ine (F := E) A => a.ρ (ineIncl h τ)
  haveI : Finite S := a.smooth.finite_range.to_subtype
  have conj_mem : ∀ (k : ℕ), ∀ s ∈ S, a.ρ (φ ^ k) * s * a.ρ ((φ ^ k)⁻¹) ∈ S := by
    rintro k _ ⟨τ, rfl⟩
    have h0 : deg (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) = 0 := by simp
    refine ⟨⟨_, deg_eq_zero_iff.mp h0⟩, ?_⟩
    simp only [← map_mul]
    exact congrArg a.ρ (Subtype.ext rfl)
  let g : ℕ → (S → S) := fun k s => ⟨_, conj_mem k s.1 s.2⟩
  obtain ⟨k1, k2, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  obtain ⟨k, m, hm, hkm⟩ : ∃ k m : ℕ, 0 < m ∧ g k = g (k + m) := by
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact ⟨k1, k2 - k1, by omega, by rw [show k1 + (k2 - k1) = k2 by omega]; exact heq⟩
    · exact ⟨k2, k1 - k2, by omega, by rw [show k2 + (k1 - k2) = k1 by omega]; exact heq.symm⟩
  have comm_ine : ∀ τ : Ine (F := E) A,
      a.ρ (φ ^ m) * a.ρ (ineIncl h τ) = a.ρ (ineIncl h τ) * a.ρ (φ ^ m) := by
    intro τ
    have e1 : a.ρ (φ ^ k * ineIncl h τ * (φ ^ k)⁻¹) =
        a.ρ (φ ^ (k + m) * ineIncl h τ * (φ ^ (k + m))⁻¹) := by
      have := congrArg Subtype.val (congrFun hkm ⟨_, τ, rfl⟩)
      rw [map_mul, map_mul, map_mul, map_mul]
      exact this
    have e2 := congrArg (fun X => a.ρ ((φ ^ k)⁻¹) * X * a.ρ (φ ^ k * φ ^ m)) e1
    simp only [← map_mul] at e2
    rw [← map_mul, ← map_mul]
    convert e2.symm using 2 <;> group
  refine ⟨m, hm, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul hφ σ
  have hc : φ ^ m * φ ^ deg σ = φ ^ deg σ * φ ^ m :=
    ((Commute.refl φ).pow_left m).zpow_right (deg σ)
  rw [hτ, map_mul, ← mul_assoc, ← map_mul, hc, map_mul, mul_assoc, comm_ine, ← mul_assoc]

/- English proof (translation)
Use `haveI := hirr`. Set `f : Representation.IntertwiningMap a.ρ a.ρ` to `⟨P, fun σ => LinearMap.ext fun v => LinearMap.congr_fun (hP σ) v⟩`. Take `⟨c, hc⟩` from `(Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := a.ρ)).2 f`. Use `⟨c, fun v => ?_⟩` and prove the remaining obligations. Use `congrArg (fun F : Representation.IntertwiningMap a.ρ a.ρ => F v) hc` as an intermediate fact.

Rewrite `this` using `[Algebra.algebraMap_eq_smul_one]`. Simplify `this.symm` using `[f]`.
-/
theorem exists_smul_of_commute {n : ℕ} (a : WDRep h (Fin n → ℂ)) (hirr : a.ρ.IsIrreducible)
    (P : Module.End ℂ (Fin n → ℂ)) (hP : ∀ σ : Weil h, P * a.ρ σ = a.ρ σ * P) :
    ∃ c : ℂ, ∀ v, P v = c • v := by
  haveI := hirr
  let f : Representation.IntertwiningMap a.ρ a.ρ :=
    ⟨P, fun σ => LinearMap.ext fun v => LinearMap.congr_fun (hP σ) v⟩
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := a.ρ)).2 f
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun F : Representation.IntertwiningMap a.ρ a.ρ => F v) hc
  rw [Algebra.algebraMap_eq_smul_one] at this
  simpa [f] using this.symm

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h x hx φ hφ α hα β hβ`. Take `⟨n, a, rfl, hirr⟩` from `hx`. Rewrite `hα`, `hβ` using `[WD.eig_mk]`. Take `⟨m, hm, hcomm⟩` from `exists_pow_central a hφ`. Take `⟨c, hc⟩` from `exists_smul_of_commute a hirr _ hcomm`.

Establish `hev : ∀ γ ∈ (a.ρ φ).charpoly.roots, γ ^ m = c`. Introduce `γ hγ`. Take `⟨v, hv⟩` from `((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr (Polynomial.isRoot_of_mem_roots hγ)).exists_hasEigenvector`. Establish `hpow : ∀ k : ℕ, ((a.ρ φ) ^ k) v = γ ^ k • v`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, map_smul, hv.apply_eq_smul, smul_smul, pow_succ]`. Establish `h1 : γ ^ m • v = c • v` using `by rw [← hpow, ← map_pow, hc]`.

Conclude with `smul_left_injective ℂ hv.2 h1`. Establish `h2 : ‖α‖ ^ m = ‖β‖ ^ m` using `by rw [← norm_pow, ← norm_pow, hev α hα, hev β hβ]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hm.ne').mp h2`.
-/
theorem irrWD_eig_norm_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), IsIrrWD x → ∀ φ : Weil h, deg φ = 1 → ∀ α ∈ x.eig φ, ∀ β ∈ x.eig φ, ‖α‖ = ‖β‖ := by
  intro E Ω _ _ _ _ _ A w h x hx φ hφ α hα β hβ
  obtain ⟨n, a, rfl, hirr⟩ := hx
  rw [WD.eig_mk] at hα hβ
  obtain ⟨m, hm, hcomm⟩ := exists_pow_central a hφ
  obtain ⟨c, hc⟩ := exists_smul_of_commute a hirr _ hcomm
  have hev : ∀ γ ∈ (a.ρ φ).charpoly.roots, γ ^ m = c := by
    intro γ hγ
    obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mpr
      (Polynomial.isRoot_of_mem_roots hγ)).exists_hasEigenvector
    have hpow : ∀ k : ℕ, ((a.ρ φ) ^ k) v = γ ^ k • v := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, map_smul, hv.apply_eq_smul, smul_smul, pow_succ]
    have h1 : γ ^ m • v = c • v := by rw [← hpow, ← map_pow, hc]
    exact smul_left_injective ℂ hv.2 h1
  have h2 : ‖α‖ ^ m = ‖β‖ ^ m := by rw [← norm_pow, ← norm_pow, hev α hα, hev β hβ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hm.ne').mp h2

end GlobalTheory.IrrWeilAbs
