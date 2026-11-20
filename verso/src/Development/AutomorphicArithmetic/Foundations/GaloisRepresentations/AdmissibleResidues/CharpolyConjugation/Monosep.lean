import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RW

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Sd UpperTheory.GalN.V

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ A w h y g hg hnd`. Proceed by induction on `y using WD.ind with`. Consider the case `hP n a`. Rewrite `hnd` using `[WD.eig_mk]`. Rewrite using `[WD.monodromyZero_ofWeilDeligneRepClass_iff]`.

Establish `key : ∀ β : ℂ, ∀ v ∈ Module.End.eigenspace (a.ρ g) β, a.N v = 0` using `fun β v hv => by`. Assume the negation of the conclusion as `h0`. Establish `hv0 : v ≠ 0` using `by rintro rfl; exact h0 (map_zero _)`. Establish `e` using `Module.End.mem_eigenspace_iff.1 hv`. Establish `hNv : a.N v ∈ Module.End.eigenspace (a.ρ g) β`.

Use `Module.End.mem_eigenspace_iff.2 ?_` and prove the remaining obligations. Use `LinearMap.congr_fun (a.comm g) v` as an intermediate fact. Simplify `this` using `[e, hg, smul_smul]`. Establish `hle : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) ≤ 1`. Establish `h1 : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) ≤ Module.finrank ℂ (Module.End.maxGenEigenspace (a.ρ g) β)` using `Submodule.finrank_mono (by first`.

Consider the case `exact (Module.End.genEigenspace (a.ρ g) β).monotone le_top`. Consider the case `exact Module.End.genEigenspace_le_maximal _ _ _`. Consider the case `exact fun x hx => Module.End.mem_maxGenEigenspace _ _ _ |>.2 ⟨1, by simpa using hx⟩)`. Rewrite `h1` using `[LinearMap.finrank_maxGenEigenspace_eq, ← Polynomial.count_roots]`. Conclude with `h1.trans (Multiset.nodup_iff_count_le_one.1 hnd β)`.

Establish `hne : Module.End.eigenspace (a.ρ g) β ≠ ⊥` using `fun hb => hv0 (by simpa [hb] using hv)`. Establish `h1 : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) = 1` using `le_antisymm hle (Submodule.one_le_finrank_iff.2 hne)`. Take `⟨c, hc⟩` from `(finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.eigenspace (a.ρ g) β) (fun hz => hv0 (congrArg Subtype.val hz))).1 h1 ⟨a.N v, hNv⟩`. Establish `hc' : a.N v = c • v` using `(congrArg Subtype.val hc).symm`. Take `⟨k, hk⟩` from `a.nilpotent`.

Establish `hpow : ∀ m : ℕ, (a.N ^ m) v = c ^ m • v` using `fun m => by`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ, Module.End.mul_apply, hc', map_smul, ih, smul_smul, pow_succ']`. Establish `hz : c ^ k • v = 0` using `by rw [← hpow k, hk]; rfl`.

Establish `hc0 : c = 0`. Break down `smul_eq_zero.1 hz with h2 | h2` into its components or cases. Use `first`. Consider the case `exact pow_eq_zero_iff (by rintro rfl; simp at h2) |>.1 h2`. Consider the case `exact eq_zero_of_pow_eq_zero h2`.

Conclude with `absurd h2 hv0`. Conclude with `h0 (by rw [hc', hc0, zero_smul])`. Establish `top : ⨆ β : ℂ, Module.End.eigenspace (a.ρ g) β = ⊤` using `(a.semisimple g).iSup_eigenspace_eq_top`. Use `LinearMap.ker_eq_top.1 (top_le_iff.1 ?_)` and prove the remaining obligations. Rewrite using `[← top]`.

Conclude with `iSup_le fun β v hv => key β v hv`.
-/
theorem UpperTheory.GalN.V.L.monosep :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 F)) (h : IsPlaceOver A w) (y : WD h) (g : ↥(Weil h)), deg g = 0 → (y.eig g).Nodup → y.mono0 := by
  intro F Ω _ _ _ _ _ A w h y g hg hnd
  induction y using WD.ind with
  | hP n a =>
    rw [WD.eig_mk] at hnd
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
    have key : ∀ β : ℂ, ∀ v ∈ Module.End.eigenspace (a.ρ g) β, a.N v = 0 := fun β v hv => by
      by_contra h0
      have hv0 : v ≠ 0 := by rintro rfl; exact h0 (map_zero _)
      have e := Module.End.mem_eigenspace_iff.1 hv
      have hNv : a.N v ∈ Module.End.eigenspace (a.ρ g) β := by
        refine Module.End.mem_eigenspace_iff.2 ?_
        have := LinearMap.congr_fun (a.comm g) v
        simpa [e, hg, smul_smul] using this
      have hle : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) ≤ 1 := by
        have h1 : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) ≤
            Module.finrank ℂ (Module.End.maxGenEigenspace (a.ρ g) β) :=
          Submodule.finrank_mono (by
            first
              | exact (Module.End.genEigenspace (a.ρ g) β).monotone le_top
              | exact Module.End.genEigenspace_le_maximal _ _ _
              | exact fun x hx => Module.End.mem_maxGenEigenspace _ _ _ |>.2 ⟨1, by simpa using hx⟩)
        rw [LinearMap.finrank_maxGenEigenspace_eq, ← Polynomial.count_roots] at h1
        exact h1.trans (Multiset.nodup_iff_count_le_one.1 hnd β)
      have hne : Module.End.eigenspace (a.ρ g) β ≠ ⊥ := fun hb => hv0 (by simpa [hb] using hv)
      have h1 : Module.finrank ℂ (Module.End.eigenspace (a.ρ g) β) = 1 :=
        le_antisymm hle (Submodule.one_le_finrank_iff.2 hne)
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.eigenspace (a.ρ g) β)
        (fun hz => hv0 (congrArg Subtype.val hz))).1 h1 ⟨a.N v, hNv⟩
      have hc' : a.N v = c • v := (congrArg Subtype.val hc).symm
      obtain ⟨k, hk⟩ := a.nilpotent
      have hpow : ∀ m : ℕ, (a.N ^ m) v = c ^ m • v := fun m => by
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, Module.End.mul_apply, hc', map_smul, ih, smul_smul, pow_succ']
      have hz : c ^ k • v = 0 := by rw [← hpow k, hk]; rfl
      have hc0 : c = 0 := by
        rcases smul_eq_zero.1 hz with h2 | h2
        · first
            | exact pow_eq_zero_iff (by rintro rfl; simp at h2) |>.1 h2
            | exact eq_zero_of_pow_eq_zero h2
        · exact absurd h2 hv0
      exact h0 (by rw [hc', hc0, zero_smul])
    have top : ⨆ β : ℂ, Module.End.eigenspace (a.ρ g) β = ⊤ := (a.semisimple g).iSup_eigenspace_eq_top
    refine LinearMap.ker_eq_top.1 (top_le_iff.1 ?_)
    rw [← top]
    exact iSup_le fun β v hv => key β v hv
