import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open Pointwise

/- English proof (translation)
Establish `h1` using `hf k g`. Rewrite `h1` using `[e, hf, hk, add_comm]`. Conclude with `(add_right_cancel h1).symm`.
-/
private theorem UpperTheory.V.Kum.coc_conj_triv {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (f : Γ → M) (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (g h k : Γ)
    (e : k * g = g * h) (hk : ∀ m, ρ k m = m) : f k = ρ g (f h) := by
  have h1 := hf k g
  rw [e, hf, hk, add_comm] at h1
  exact (add_right_cancel h1).symm

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l _ D e`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨p1, p2, p3, p4⟩` from `placeDict F Ω`. Establish `hchi : ∀ g : G F Ω, D.chi (toGS Ω _ g) = cycZ F Ω l g` using `fun g => DFunLike.congr_fun D.hchi g`.

Establish `htriv : ∀ g : G F Ω, cycZ F Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m` using `fun g hg m => by`. Rewrite using `[qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]`. Establish `hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b)` using `z.2.2`. Establish `hconj : ∀ g h k : G F Ω, k * g = g * h → cycZ F Ω l k = 1 → z.1 (toGS Ω _ k) = qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ h))` using `fun g h k e1 hk => coc_conj_triv _ _ hz _ _ _ (by rw [← map_mul, ← map_mul, e1]) (htriv k hk)`. Establish `h1 : z.1 1 = 0`.

Use `hz 1 1` as an intermediate fact. Rewrite `this` using `[one_mul, map_one]`. Conclude with `left_eq_add.1 this`. Establish `hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ u : Uinf F Ω l, u.1 ∈ Dec (F` using `F) A → z.1 (toGS Ω _ u.1) = 0 := by`. Introduce `A hA u hu`.

Take `⟨v, hv⟩` from `p2 A (p3 A l (Fact.out : l.Prime).ne_zero hA)`. Establish `hvS : v ∈ D.S`. Use `(p4 A v l hv).1 hA` as an intermediate fact. Rewrite `this` using `[← D.hS]`. Conclude with `this`.

Take `⟨g, rfl⟩` from `exists_smul_eq_of_isPlaceOver (F := F) (D.hA ⟨v, hvS⟩) hv`. Take `⟨m, hm⟩` from `(res_mk_eq_zero_iff D e ⟨v, hvS⟩ z).1 ((mem_Sha_iff D e _).1 hx ⟨v, hvS⟩)`. Establish `hc : g⁻¹ * u.1 * g ∈ Dec (F` using `F) (D.A ⟨v, hvS⟩) := by`. Establish `h : u.1 • g • D.A ⟨v, hvS⟩ = g • D.A ⟨v, hvS⟩` using `hu`. Use `show (g⁻¹ * u.1 * g) • D.A ⟨v, hvS⟩ = D.A ⟨v, hvS⟩`.

Rewrite using `[mul_smul, mul_smul, h, inv_smul_smul]`. Establish `hu1 : cycZ F Ω l u.1 = 1` using `u.2.2`. Establish `h2` using `hm ⟨_, hc⟩`. Rewrite `h2` using `[htriv _ (by simp [hu1]), sub_self]`. Rewrite using `[hconj g (g⁻¹ * u.1 * g) u.1 (by group) hu1, h2, map_zero]`.

Use `⟨⟨?_, fun a b => ?_, fun A u hu => ?_, hdec⟩, (Submodule.mem_iInf _).2 fun g u u' h => ?_⟩` and prove the remaining obligations. Conclude with `(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp ((continuous_toGS Ω _).comp continuous_subtype_val))`. Rewrite using `[resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]`. Rewrite using `[resInf_mk]`. Distinguish the cases in `hA : A = ⊤`.

Substitute `hA` using the available equality. Rewrite `hu` using `[p1, Subgroup.mem_bot]`. Rewrite using `[hu, map_one, h1]`. Take `⟨v, hv⟩` from `p2 A hA`. Distinguish the cases in `hl : A.valuation (l : Ω) < 1`.

Conclude with `hdec A hl u (Ine_le_Dec A hu)`. Establish `hvS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 F)))`. Rewrite using `[D.hS]`. Conclude with `fun h => hl ((p4 A v l hv).2 h)`. Establish `hn : u.1 ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))`.

Apply `Subgroup.le_topologicalClosure` to reduce the goal to its premises. Apply `Subgroup.subset_normalClosure` to reduce the goal to its premises. Simplify using `only [Set.mem_iUnion]`. Conclude with `⟨v, hvS, A, hv, hu⟩`. Establish `: toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) u.1 = 1` using `(QuotientGroup.eq_one_iff _).2 hn`.

Rewrite using `[this, h1]`. Rewrite using `[resInf_mk, resInf_mk, hconj g u.1 u'.1 (AlgEquiv.ext h) u'.2.2, qzTw_apply, hchi]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Kum.resInfMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), (Sha D e).map (resInf D e) ≤ EqHom l (Uinf F Ω l) (qzG F Ω l e) := by
  intro F Ω _ _ _ _ _ l _ D e
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨p1, p2, p3, p4⟩ := placeDict F Ω
  have hchi : ∀ g : G F Ω, D.chi (toGS Ω _ g) = cycZ F Ω l g := fun g => DFunLike.congr_fun D.hchi g
  have htriv : ∀ g : G F Ω, cycZ F Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
    rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
  have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
  have hconj : ∀ g h k : G F Ω, k * g = g * h → cycZ F Ω l k = 1 →
      z.1 (toGS Ω _ k) = qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ h)) := fun g h k e1 hk =>
    coc_conj_triv _ _ hz _ _ _ (by rw [← map_mul, ← map_mul, e1]) (htriv k hk)
  have h1 : z.1 1 = 0 := by
    have := hz 1 1
    rw [one_mul, map_one] at this
    exact left_eq_add.1 this
  have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ u : Uinf F Ω l, u.1 ∈ Dec (F := F) A →
      z.1 (toGS Ω _ u.1) = 0 := by
    intro A hA u hu
    obtain ⟨v, hv⟩ := p2 A (p3 A l (Fact.out : l.Prime).ne_zero hA)
    have hvS : v ∈ D.S := by
      have := (p4 A v l hv).1 hA
      rw [← D.hS] at this
      exact this
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA ⟨v, hvS⟩) hv
    obtain ⟨m, hm⟩ := (res_mk_eq_zero_iff D e ⟨v, hvS⟩ z).1 ((mem_Sha_iff D e _).1 hx ⟨v, hvS⟩)
    have hc : g⁻¹ * u.1 * g ∈ Dec (F := F) (D.A ⟨v, hvS⟩) := by
      have h : u.1 • g • D.A ⟨v, hvS⟩ = g • D.A ⟨v, hvS⟩ := hu
      show (g⁻¹ * u.1 * g) • D.A ⟨v, hvS⟩ = D.A ⟨v, hvS⟩
      rw [mul_smul, mul_smul, h, inv_smul_smul]
    have hu1 : cycZ F Ω l u.1 = 1 := u.2.2
    have h2 := hm ⟨_, hc⟩
    rw [htriv _ (by simp [hu1]), sub_self] at h2
    rw [hconj g (g⁻¹ * u.1 * g) u.1 (by group) hu1, h2, map_zero]
  refine ⟨⟨?_, fun a b => ?_, fun A u hu => ?_, hdec⟩, (Submodule.mem_iInf _).2 fun g u u' h => ?_⟩
  · exact (IsLocallyConstant.iff_continuous _).2
      (z.2.1.comp ((continuous_toGS Ω _).comp continuous_subtype_val))
  · rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]
  · rw [resInf_mk]
    by_cases hA : A = ⊤
    · subst hA
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, h1]
    obtain ⟨v, hv⟩ := p2 A hA
    by_cases hl : A.valuation (l : Ω) < 1
    · exact hdec A hl u (Ine_le_Dec A hu)
    have hvS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [D.hS]
      exact fun h => hl ((p4 A v l hv).2 h)
    have hn : u.1 ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hu⟩
    have : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) u.1 = 1 := (QuotientGroup.eq_one_iff _).2 hn
    rw [this, h1]
  · rw [resInf_mk, resInf_mk, hconj g u.1 u'.1 (AlgEquiv.ext h) u'.2.2, qzTw_apply, hchi]
    rfl
