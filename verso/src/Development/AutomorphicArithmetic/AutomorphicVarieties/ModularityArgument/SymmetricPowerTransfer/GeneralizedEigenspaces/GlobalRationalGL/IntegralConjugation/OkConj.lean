import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.EStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.AdSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.ExistsUnitNormQuotientLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.LocBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.GlobalRationalGL.IntegralConjugation.UaFacts

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil Formalism.BasicNotions Matrix
open UpperTheory.V UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob
open UpperTheory.V.W (Plc Lp)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Dict.Br

/- English proof (translation)
Establish `h1` using `HeightOneSpectrum.Support.finite (𝓞 F) a`. Establish `h2` using `HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹`. Establish `h3 : ((HeightOneSpectrum.Support (𝓞 F) a) ∪ (HeightOneSpectrum.Support (𝓞 F) a⁻¹))ᶜ ∈ Filter.cofinite (α` using `Pl F) := by`. Rewrite using `[Filter.mem_cofinite, compl_compl]`. Conclude with `h1.union h2`.

Use `filter_upwards [h3] with v hv`. Simplify using `only [Set.mem_compl_iff, Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv`. Apply `le_antisymm hv.1` to reduce the goal to its premises. Use `hv.2` as an intermediate fact. Rewrite `this` using `[map_inv₀]`.

Establish `h0 : v.valuation F a ≠ 0` using `by simpa using ha`. Conclude with `(inv_le_one₀ (zero_lt_iff.2 h0)).1 this`.
-/
private theorem cof_val (F : Type) [Field F] [NumberField F] (a : F) (ha : a ≠ 0) :
    ∀ᶠ v : Pl F in Filter.cofinite, v.valuation F a = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 F) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 F) a⁻¹
  have h3 : ((HeightOneSpectrum.Support (𝓞 F) a) ∪ (HeightOneSpectrum.Support (𝓞 F) a⁻¹))ᶜ ∈ Filter.cofinite (α := Pl F) := by
    rw [Filter.mem_cofinite, compl_compl]
    exact h1.union h2
  filter_upwards [h3] with v hv
  simp only [Set.mem_compl_iff, Set.mem_union, not_or, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  apply le_antisymm hv.1
  have := hv.2
  rw [map_inv₀] at this
  have h0 : v.valuation F a ≠ 0 := by simpa using ha
  exact (inv_le_one₀ (zero_lt_iff.2 h0)).1 this

/- English proof (translation)
Establish `h1 : Valued.v (cv v a) = 1`. Rewrite using `[← h]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a`. Establish `h0 : cv v a ≠ 0`. Introduce `h0`.

Rewrite `h1` using `[h0]`. Simplify using `at h1`. Establish `h2 : Valued.v (cv v a)⁻¹ = 1` using `by rw [map_inv₀, h1, inv_one]`. Use `⟨⟨⟨cv v a, h1.le⟩, ⟨(cv v a)⁻¹, h2.le⟩, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `Subtype.ext (mul_inv_cancel₀ h0)`.

Conclude with `Subtype.ext (inv_mul_cancel₀ h0)`.
-/
private theorem unit_of_val (F : Type) [Field F] [NumberField F] (v : Pl F) (a : F) (h : v.valuation F a = 1) :
    ∃ u : (Ov v)ˣ, algebraMap (Ov v) (Kv v) u = cv v a := by
  have h1 : Valued.v (cv v a) = 1 := by
    rw [← h]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  have h0 : cv v a ≠ 0 := by
    intro h0
    rw [h0] at h1
    simp at h1
  have h2 : Valued.v (cv v a)⁻¹ = 1 := by rw [map_inv₀, h1, inv_one]
  refine ⟨⟨⟨cv v a, h1.le⟩, ⟨(cv v a)⁻¹, h2.le⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ h0)
  · exact Subtype.ext (inv_mul_cancel₀ h0)

/- English proof (translation)
Establish `key : R * P = Q * R`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, hP, hQ, hR, ← Matrix.map_mul, ← Matrix.map_mul]`. Use `congr 1`. Establish `: (Y : Matrix (Fin 2) (Fin 2) A) * ((Y⁻¹ * G * Y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = (G : Matrix (Fin 2) (Fin 2) A) * (Y : Matrix (Fin 2) (Fin 2) A)`.

Rewrite using `[← Units.val_mul, ← Units.val_mul]`. Use `congr 1`. Use `group`. Rewrite using `[Matrix.smul_mul, this, Matrix.mul_smul]`. Rewrite using `[mul_assoc, eq_inv_mul_iff_mul_eq, key]`.
-/
private theorem conj_cmp {A A' : Type} [CommRing A] [CommRing A'] (ρ : A →+* A') (c : A)
    (Y G : GL (Fin 2) A) (P Q R : GL (Fin 2) A')
    (hP : (P : Matrix (Fin 2) (Fin 2) A') = (((Y⁻¹ * G * Y : GL (Fin 2) A)) : Matrix (Fin 2) (Fin 2) A).map ρ)
    (hQ : (Q : Matrix (Fin 2) (Fin 2) A') = (G : Matrix (Fin 2) (Fin 2) A).map ρ)
    (hR : (R : Matrix (Fin 2) (Fin 2) A') = (c • (Y : Matrix (Fin 2) (Fin 2) A)).map ρ) :
    P = R⁻¹ * Q * R := by
  have key : R * P = Q * R := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hP, hQ, hR, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    have : (Y : Matrix (Fin 2) (Fin 2) A) * ((Y⁻¹ * G * Y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = (G : Matrix (Fin 2) (Fin 2) A) * (Y : Matrix (Fin 2) (Fin 2) A) := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.smul_mul, this, Matrix.mul_smul]
  rw [mul_assoc, eq_inv_mul_iff_mul_eq, key]

end UpperTheory.V.Z.Sym.Dict.Br

/- English proof (translation)
Introduce `L _ _ _ B x hx`. Take `⟨X, hXu, hXi, hXw⟩` from `adSurj L B.toRingBr 2 x`. Establish `hΔ : B.Δ ≠ 0`. Introduce `h0`. Establish `hω : (QuadraticAlgebra.omega : Lsq (Lp L) B.Δ) * QuadraticAlgebra.omega = 0`.

Apply the tactic sequence `ext <;> simp [h0]`. Establish `h1 : B.e QuadraticAlgebra.omega * B.e QuadraticAlgebra.omega = 0`. Rewrite using `[← map_mul, hω, map_zero]`. Establish `h2 : B.e QuadraticAlgebra.omega = 0` using `mul_self_eq_zero.1 h1`. Establish `h3 : (QuadraticAlgebra.omega : Lsq (Lp L) B.Δ) = 0` using `(map_eq_zero_iff _ B.e.injective).1 h2`.

Simplify using `using congrArg QuadraticAlgebra.im h3`. Establish `h2F : (2 : Lp L) ≠ 0` using `two_ne_zero`. Establish `h2 : ∀ v : Pl (Lp L), (2 : Kv v) ≠ 0`. Introduce `v h0`. Apply `h2F` to reduce the goal to its premises.

Apply `(cv v).injective` to reduce the goal to its premises. Rewrite using `[map_ofNat, map_zero, h0]`. Establish `hΔv : ∀ v : Pl (Lp L), cv v B.Δ ≠ 0` using `fun v h0 => hΔ ((map_eq_zero _).1 h0)`. Use `choose Y c hYc hY1 hYK using fun v : Pl (Lp L) => h90 (Ov v) (Kv v) (cv v B.Δ) (h2 v) (hΔv v) (X v) (hXu v)`. Establish `hYA : Y ∈ RP (fun v : Pl (Lp L) => DX (cv v B.Δ)) fun v => KD (cv v B.Δ) (Ov v)` using `by show ∀ᶠ v in Filter.cofinite, Y v ∈ KD (cv v B.Δ) (Ov v) filter_upwards [hXi, cof_val (Lp L) B.Δ hΔ, cof_val (Lp L) 2 h2F] with v hi hv h2v`.

Take `⟨h1, -, -, h4⟩` from `locBase (Lp L) v`. Use `haveI := h1`. Establish `h2n : (2 : 𝓞 (Lp L)) ∉ v.asIdeal`. Introduce `hm`. Use `(HeightOneSpectrum.valuation_lt_one_iff_mem (K := Lp L) v (2 : 𝓞 (Lp L))).2 hm` as an intermediate fact.

Simplify using `only [map_ofNat] at this`. Conclude with `this.ne h2v`. Conclude with `hYK v (h4 h2n) (unit_of_val (Lp L) v B.Δ hv) hi`. Use `⟨⟨Y, hYA⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv`.

Apply `hY1 v` to reduce the goal to its premises. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Apply `B.ρ_inj v` to reduce the goal to its premises. Introduce `w h`.

Substitute `h` using the available equality. Use `hXw w` as an intermediate fact. Establish `h3 : mL w x = 1`. Simplify using `only [mL, hv w rfl]`. Both sides reduce to the same expression.

Rewrite using `[map_sub, sub_eq_zero]`. Establish `h4` using `congrFun (congrFun (this.symm.trans h3) i) j`. Rewrite `h4` using `[Matrix.map_apply]`. Rewrite using `[h4]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij]`. Introduce `g`. Establish `hmem : ((⟨Y, hYA⟩ : DA B.Δ)⁻¹ * (g : DA B.Δ) * ⟨Y, hYA⟩) ∈ SA B.Δ`.

Establish `hg` using `g.2`. Simplify using `only [SA, Subgroup.mem_iInf] at hg ⊢`. Introduce `v`. Use `hg v` as an intermediate fact. Simplify using `only [Subgroup.mem_comap, SU, MonoidHom.mem_ker, MonoidHom.comp_apply] at this ⊢`.

Simplify using `only [map_mul, map_inv, this, mul_one, inv_mul_cancel]`. Use `⟨⟨_, hmem⟩, rfl, ?_⟩` and prove the remaining obligations. Establish `hF` using `(uaFacts L 2)`. Establish `hext` using `hF.2.2.2.2.1`. Establish `hfin` using `hF.2.2.2.2.2.1`.

Apply `hext` to reduce the goal to its premises. Introduce `w`. Rewrite using `[map_mul, map_mul, map_inv]`. Apply `conj_cmp (B.ρ _ w rfl) (c (un w) : Lsq (Kv (un w)) (cv (un w) B.Δ)) ((Y (un w) : DX _) : GL (Fin 2) _) (((g : DA B.Δ).1 (un w) : DX _) : GL (Fin 2) _)` to reduce the goal to its premises. Conclude with `B.bS_loc _ w`.

Conclude with `B.bS_loc _ w`. Rewrite using `[← hYc]`. Conclude with `hXw w`. Introduce `τ`. Establish `a1` using `((hfin _).1.1 (B.bS ⟨_, hmem⟩).2.1) τ`.

Establish `a2` using `((hfin _).1.1 (B.bS g).2.1) τ`. Establish `a3` using `((hfin _).1.1 hx) τ`. Rewrite using `[a1, map_mul, map_mul, map_inv, a2, a3]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Z.Sym.Dict.Br.okConj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (B : Bridge L), ∀ x ∈ finU L 2, ∃ y : DA B.Δ, (∀ v, (∀ w, un w = v → cLoc w x = 1) → y.1 v = 1) ∧ ∀ g : SA B.Δ, ∃ g' : SA B.Δ, (g' : DA B.Δ) = y⁻¹ * g * y ∧ (B.bS g' : UA L 2) = x⁻¹ * B.bS g * x := by
  intro L _ _ _ B x hx
  obtain ⟨X, hXu, hXi, hXw⟩ := adSurj L B.toRingBr 2 x
  have hΔ : B.Δ ≠ 0 := by
    intro h0
    have hω : (QuadraticAlgebra.omega : Lsq (Lp L) B.Δ) * QuadraticAlgebra.omega = 0 := by
      ext <;> simp [h0]
    have h1 : B.e QuadraticAlgebra.omega * B.e QuadraticAlgebra.omega = 0 := by
      rw [← map_mul, hω, map_zero]
    have h2 : B.e QuadraticAlgebra.omega = 0 := mul_self_eq_zero.1 h1
    have h3 : (QuadraticAlgebra.omega : Lsq (Lp L) B.Δ) = 0 := (map_eq_zero_iff _ B.e.injective).1 h2
    simpa using congrArg QuadraticAlgebra.im h3
  have h2F : (2 : Lp L) ≠ 0 := two_ne_zero
  have h2 : ∀ v : Pl (Lp L), (2 : Kv v) ≠ 0 := by
    intro v h0
    apply h2F
    apply (cv v).injective
    rw [map_ofNat, map_zero, h0]
  have hΔv : ∀ v : Pl (Lp L), cv v B.Δ ≠ 0 := fun v h0 => hΔ ((map_eq_zero _).1 h0)
  choose Y c hYc hY1 hYK using fun v : Pl (Lp L) => h90 (Ov v) (Kv v) (cv v B.Δ) (h2 v) (hΔv v) (X v) (hXu v)
  have hYA : Y ∈ RP (fun v : Pl (Lp L) => DX (cv v B.Δ)) fun v => KD (cv v B.Δ) (Ov v) := by
    show ∀ᶠ v in Filter.cofinite, Y v ∈ KD (cv v B.Δ) (Ov v)
    filter_upwards [hXi, cof_val (Lp L) B.Δ hΔ, cof_val (Lp L) 2 h2F] with v hi hv h2v
    obtain ⟨h1, -, -, h4⟩ := locBase (Lp L) v
    haveI := h1
    have h2n : (2 : 𝓞 (Lp L)) ∉ v.asIdeal := by
      intro hm
      have := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := Lp L) v (2 : 𝓞 (Lp L))).2 hm
      simp only [map_ofNat] at this
      exact this.ne h2v
    exact hYK v (h4 h2n) (unit_of_val (Lp L) v B.Δ hv) hi
  refine ⟨⟨Y, hYA⟩, ?_, ?_⟩
  · intro v hv
    apply hY1 v
    refine Matrix.ext fun i j => ?_
    rw [← sub_eq_zero]
    apply B.ρ_inj v
    intro w h
    subst h
    have := hXw w
    have h3 : mL w x = 1 := by
      simp only [mL, hv w rfl]
      rfl
    rw [map_sub, sub_eq_zero]
    have h4 := congrFun (congrFun (this.symm.trans h3) i) j
    rw [Matrix.map_apply] at h4
    rw [h4]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  · intro g
    have hmem : ((⟨Y, hYA⟩ : DA B.Δ)⁻¹ * (g : DA B.Δ) * ⟨Y, hYA⟩) ∈ SA B.Δ := by
      have hg := g.2
      simp only [SA, Subgroup.mem_iInf] at hg ⊢
      intro v
      have := hg v
      simp only [Subgroup.mem_comap, SU, MonoidHom.mem_ker, MonoidHom.comp_apply] at this ⊢
      simp only [map_mul, map_inv, this, mul_one, inv_mul_cancel]
    refine ⟨⟨_, hmem⟩, rfl, ?_⟩
    have hF := (uaFacts L 2)
    have hext := hF.2.2.2.2.1
    have hfin := hF.2.2.2.2.2.1
    apply hext
    · intro w
      rw [map_mul, map_mul, map_inv]
      apply conj_cmp (B.ρ _ w rfl) (c (un w) : Lsq (Kv (un w)) (cv (un w) B.Δ)) ((Y (un w) : DX _) : GL (Fin 2) _) (((g : DA B.Δ).1 (un w) : DX _) : GL (Fin 2) _)
      · exact B.bS_loc _ w
      · exact B.bS_loc _ w
      · rw [← hYc]
        exact hXw w
    · intro τ
      have a1 := ((hfin _).1.1 (B.bS ⟨_, hmem⟩).2.1) τ
      have a2 := ((hfin _).1.1 (B.bS g).2.1) τ
      have a3 := ((hfin _).1.1 hx) τ
      rw [a1, map_mul, map_mul, map_inv, a2, a3]
      simp
