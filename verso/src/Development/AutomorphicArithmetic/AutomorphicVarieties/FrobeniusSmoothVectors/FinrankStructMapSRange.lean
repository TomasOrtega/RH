import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrameExtensionOfLocallyConstant

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ k _ _ F C₀ hF`. Establish `h2 : (2 : k) ≠ 0`. Introduce `h`. Establish `h' : ((2 : ℕ) : k) = 0` using `by exact_mod_cast h`. Rewrite `h'` using `[CharP.cast_eq_zero_iff k l]`.

Conclude with `hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h')`. Use `set χ := F.Ψ⁻¹ ^ 2 * F.delK k with hχ`. Establish `hc : ((χ F.c : kˣ) : k) = -1`. Simplify using `[hχ, Frame.delK, hF.del_c, hF.Ψ_c]`. Set `Z` to `Z1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)`.

Set `f : Z →ₗ[k] (F.G0 → k)` to `{ toFun := fun x g => (x.1.1 g + ((χ g : k) * x.1.1 F.c - x.1.1 F.c) * 2⁻¹) * (F.Ψ g : k) map_add' := by`. Introduce `x y`. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Use the proof step `map_smul' := by`. Introduce `r x`. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules. Use `ring }`.

Establish `hker : Submodule.comap Z.subtype (continuousCoboundaries1 (chRep χ) fun _ => (⊥ : Submodule k k)) ≤ LinearMap.ker f`. Introduce and unpack `⟨x, hx⟩ hb`. Rewrite `hb` using `[Submodule.mem_comap]`. Take `⟨X, hX, -⟩` from `hb`. Rewrite using `[LinearMap.mem_ker]`.

Use function extensionality and compare the values at `g`. Establish `e1` using `hX (g : F.Γ)`. Establish `e2` using `hX F.c`. Simplify using `only [Submodule.subtype_apply, chRep_apply, hc] at e1 e2`. Simplify using `only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]`.

Rewrite using `[e1, e2]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Set `L` to `Submodule.liftQ _ f hker`. Establish `hle : F.strS k ≤ LinearMap.range L`.

Introduce `a ha`. Take `⟨x, hx, hx0, hax⟩` from `frame_extension_of_locallyConstant hF a ha`. Use `⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.liftQ_apply]`. Use function extensionality and compare the values at `g`.

Simplify using `[f, hx0, hax]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Fr.finrank_structMapS_range :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → Module.rank k (F.strS k) ≤ C₀ := by
  intro l _ k _ _ F C₀ hF
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k l] at h'
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) Nat.prime_two).mp h')
  set χ := F.Ψ⁻¹ ^ 2 * F.delK k with hχ
  have hc : ((χ F.c : kˣ) : k) = -1 := by
    simp [hχ, Frame.delK, hF.del_c, hF.Ψ_c]
  let Z := Z1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)
  let f : Z →ₗ[k] (F.G0 → k) :=
    { toFun := fun x g => (x.1.1 g + ((χ g : k) * x.1.1 F.c - x.1.1 F.c) * 2⁻¹) * (F.Ψ g : k)
      map_add' := by
        intro x y
        funext g
        simp
        ring
      map_smul' := by
        intro r x
        funext g
        simp
        ring }
  have hker : Submodule.comap Z.subtype (continuousCoboundaries1 (chRep χ) fun _ => (⊥ : Submodule k k)) ≤ LinearMap.ker f := by
    rintro ⟨x, hx⟩ hb
    rw [Submodule.mem_comap] at hb
    obtain ⟨X, hX, -⟩ := hb
    rw [LinearMap.mem_ker]
    funext g
    have e1 := hX (g : F.Γ)
    have e2 := hX F.c
    simp only [Submodule.subtype_apply, chRep_apply, hc] at e1 e2
    simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    rw [e1, e2]
    field_simp
    ring
  let L := Submodule.liftQ _ f hker
  have hle : F.strS k ≤ LinearMap.range L := by
    intro a ha
    obtain ⟨x, hx, hx0, hax⟩ := frame_extension_of_locallyConstant hF a ha
    refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    funext g
    simp [f, hx0, hax]
  calc Module.rank k (F.strS k) ≤ Module.rank k (LinearMap.range L) := Submodule.rank_mono hle
    _ ≤ Module.rank k (H1C F.loc (chRep χ) fun _ => (⊥ : Submodule k k)) := rank_range_le L
    _ ≤ C₀ := hF.b1p
