import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Take `⟨z0, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨m, hm⟩` from `h2 (-(z0.1 c))`. Establish `hB : d0 ρ m ∈ Z1 ρ` using `coboundaries_le_cocycles ρ hρ (LinearMap.mem_range_self _ m)`. Use `⟨z0 - ⟨d0 ρ m, hB⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.Quotient.eq, Submodule.mem_comap, sub_sub_cancel_left, map_neg]`.

Conclude with `Submodule.neg_mem _ ⟨m, rfl⟩`. Use `show z0.1 c - d0 ρ m c = 0`. Rewrite using `[amitsur_d0_apply, hc]`. Establish `hm' : m + m = -(z0.1 c)` using `hm`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_norm {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (hρ : ContAction ρ)
    (h2 : Function.Surjective fun m : M => m + m) (c : Γ) (hc : ∀ m, ρ c m = -m) (x : H1 ρ) :
    ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 c = 0 := by
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := h2 (-(z0.1 c))
  have hB : d0 ρ m ∈ Z1 ρ := coboundaries_le_cocycles ρ hρ (LinearMap.mem_range_self _ m)
  refine ⟨z0 - ⟨d0 ρ m, hB⟩, ?_, ?_⟩
  · rw [Submodule.Quotient.eq, Submodule.mem_comap, sub_sub_cancel_left, map_neg]
    exact Submodule.neg_mem _ ⟨m, rfl⟩
  · show z0.1 c - d0 ρ m c = 0
    rw [amitsur_d0_apply, hc]
    have hm' : m + m = -(z0.1 c) := hm
    calc z0.1 c - (-m - m) = z0.1 c + (m + m) := by abel
      _ = 0 := by rw [hm']; abel

/- English proof (translation)
Introduce `Ω _ _ _ l _ R M _ _ _ _ _ S ρ hρ hbij c hcneg Av hAv v0 hlv0 P K hK L hL hP`. Establish `hex : ∀ x : H1 ρ, ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 (toGS Ω _ c) = 0` using `fun x => exists_norm ρ hρ hbij.2 (toGS Ω _ c) hcneg x`. Establish `hA : ∀ x : H1 ρ, x ∈ Sel ρ (locFam S Av) (continuous_locFam S Av) L → ∀ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x → z.1 (toGS Ω _ c) = 0 → (fun g => z.1 (toGS Ω _ g)) ∈ Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F` using `ℚ) (Av v0)) P := by`. Introduce `x hx z hzx hzc`. Substitute `hzx` using the available equality.

Establish `hcoc : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h)` using `((mem_Z1_iff_cocycle _ _).mp z.2).2`. Establish `hz1 : z.1 1 = 0`. Establish `h` using `hcoc 1 1`. Rewrite `h` using `[one_mul, map_one, Module.End.one_apply]`. Simplify using `using h`.

Establish `hmemv : ∀ v, (Submodule.Quotient.mk (restrictCocycles1 ρ (locFam S Av v) (continuous_locFam S Av v) z) : H1 (ρ.comp (locFam S Av v))) ∈ L v` using `fun v => (mem_Sel _ _ _ _ _).mp hx v`. Take `⟨y, hy⟩` from `hP _ (hmemv v0)`. Use `⟨y, ⟨?_, ?_, hzc, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `((IsLocallyConstant.iff_continuous _).mpr ((mem_Z1_iff_cocycle _ _).mp z.2).1).comp_continuous continuous_quot_mk`. Introduce `g h show z.1 (toGS Ω _ (g * h)) = z.1 (toGS Ω _ g) + ρ (toGS Ω _ g) (z.1 (toGS Ω _ h))`.

Rewrite using `[map_mul]`. Conclude with `hcoc _ _`. Introduce and unpack `g ⟨hgK, A, hAl, hgA⟩ show z.1 (toGS Ω _ g) = 0`. Distinguish the cases in `hAtop : A = ⊤`. Substitute `hAtop` using the available equality.

Rewrite `hgA` using `[(UpperTheory.V.Kum.placeDict ℚ Ω).1, Subgroup.mem_bot]`. Rewrite using `[hgA, map_one, hz1]`. Take `⟨v, hAv'⟩` from `(UpperTheory.V.Kum.placeDict ℚ Ω).2.1 A hAtop`. Distinguish the cases in `hvS : v ∈ S`. Use `set w : S := ⟨v, hvS⟩`.

Establish `hne : w ≠ v0`. Introduce `hw`. Apply `hAl` to reduce the goal to its premises. Establish `h` using `(hAv' (l : 𝓞 ℚ)).mpr (by rw [show v = v0.1 from congrArg Subtype.val hw]; exact hlv0)`. Simplify using `using h`.

Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver (hAv w) hAv'`. Rewrite `hgA` using `[← hσ]`. Establish `hgA' : σ⁻¹ * g * σ ∈ Ine (F` using `ℚ) (Av w) := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hgA`. Establish `hur` using `hL w hne (hmemv w)`. Rewrite `hur` using `[H1ur, LinearMap.mem_ker]`.

Establish `hur'` using `(Submodule.Quotient.mk_eq_zero _).mp hur`. Rewrite `hur'` using `[Submodule.mem_comap]`. Take `⟨m, hm⟩` from `hur'`. Establish `hj` using `congrFun hm ⟨⟨σ⁻¹ * g * σ, Ine_le_Dec _ hgA'⟩, hgA'⟩`. Rewrite `hj` using `[amitsur_d0_apply]`.

Establish `hconj : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = 0`. Establish `hj' : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = ρ (toGS Ω _ (σ⁻¹ * g * σ)) m - m` using `hj.symm`. Rewrite using `[hj']`. Rewrite using `[map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, show ρ (toGS Ω _ g) (ρ (toGS Ω _ σ) m) = ρ (toGS Ω _ σ) m from hK g hgK _, ← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel, map_one, Module.End.one_apply, sub_self]`. Use `set a := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ`.

Use `set b := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g`. Establish `hb : ∀ m, ρ b m = m` using `hK g hgK`. Rewrite `hconj` using `[map_mul, map_mul, map_inv]`. Establish `e1` using `hcoc (a⁻¹ * b) a`. Establish `e2` using `hcoc a⁻¹ b`.

Establish `e3` using `hcoc a⁻¹ a`. Rewrite `e3` using `[inv_mul_cancel, hz1]`. Rewrite `e1` using `[map_mul, Module.End.mul_apply, hb, e2, hconj]`. Establish `hinv0 : ρ a⁻¹ (z.1 b) = 0`. Establish `: (0 : M) = ρ a⁻¹ (z.1 b) + (z.1 a⁻¹ + ρ a⁻¹ (z.1 a))` using `by rw [e1]; abel`.

Rewrite `this` using `[← e3, add_zero]`. Conclude with `this.symm`. Establish `: z.1 b = ρ a (ρ a⁻¹ (z.1 b))`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Rewrite using `[this, hinv0, map_zero]`.

Establish `hgN : g ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))` using `Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (Set.mem_iUnion₂.mpr ⟨v, hvS, Set.mem_iUnion₂.mpr ⟨A, hAv', hgA⟩⟩))`. Rewrite using `[show toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g = 1 from (QuotientGroup.eq_one_iff g).mpr hgN, hz1]`. Introduce `h hh`. Conclude with `hy ⟨h, hh⟩`. Use `choose zc hzc using hex`.

Use `⟨fun x => ⟨fun g => (zc x.1).1 (toGS Ω _ g), hA x.1 x.2 (zc x.1) (hzc x.1).1 (hzc x.1).2⟩, ?_⟩` and prove the remaining obligations. Introduce `x x' hxx`. Establish `hfun : (fun g => (zc x.1).1 (toGS Ω _ g)) = (fun g => (zc x'.1).1 (toGS Ω _ g))` using `congrArg Subtype.val hxx`. Establish `hz : zc x.1 = zc x'.1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `q`. Take `⟨g, rfl⟩` from `QuotientGroup.mk'_surjective (NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) q`. Conclude with `congrFun hfun g`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← (hzc x.1).1, ← (hzc x'.1).1, hz]`.
-/
theorem UpperTheory.V.Ws.Bl.selToZc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → (Function.Bijective fun m : M => m + m) →
          ∀ c : G ℚ Ω, (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ v0 : S, ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal → ∀ (P : Set M) (K : Subgroup (G ℚ Ω)), (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → L v ≤ H1ur (ρ.comp (locFam S Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) →
          (∀ z : Z1 (ρ.comp (locFam S Av v0)), (Submodule.Quotient.mk z : H1 (ρ.comp (locFam S Av v0))) ∈ L v0 → ∃ y, ∀ h, z.1 h - (ρ (locFam S Av v0 h) y - y) ∈ P) →
          ∃ f : Sel ρ (locFam S Av) (continuous_locFam S Av) L → Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P, Function.Injective f := by
  intro Ω _ _ _ l _ R M _ _ _ _ _ S ρ hρ hbij c hcneg Av hAv v0 hlv0 P K hK L hL hP
  have hex : ∀ x : H1 ρ, ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 (toGS Ω _ c) = 0 :=
    fun x => exists_norm ρ hρ hbij.2 (toGS Ω _ c) hcneg x
  have hA : ∀ x : H1 ρ, x ∈ Sel ρ (locFam S Av) (continuous_locFam S Av) L → ∀ z : Z1 ρ,
      (Submodule.Quotient.mk z : H1 ρ) = x → z.1 (toGS Ω _ c) = 0 →
      (fun g => z.1 (toGS Ω _ g)) ∈ Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P := by
    intro x hx z hzx hzc
    subst hzx
    have hcoc : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := ((mem_Z1_iff_cocycle _ _).mp z.2).2
    have hz1 : z.1 1 = 0 := by
      have h := hcoc 1 1
      rw [one_mul, map_one, Module.End.one_apply] at h
      simpa using h
    have hmemv : ∀ v, (Submodule.Quotient.mk (restrictCocycles1 ρ (locFam S Av v) (continuous_locFam S Av v) z) :
        H1 (ρ.comp (locFam S Av v))) ∈ L v := fun v => (mem_Sel _ _ _ _ _).mp hx v
    obtain ⟨y, hy⟩ := hP _ (hmemv v0)
    refine ⟨y, ⟨?_, ?_, hzc, ?_, ?_⟩⟩
    · exact ((IsLocallyConstant.iff_continuous _).mpr ((mem_Z1_iff_cocycle _ _).mp z.2).1).comp_continuous
        continuous_quot_mk
    · intro g h
      show z.1 (toGS Ω _ (g * h)) = z.1 (toGS Ω _ g) + ρ (toGS Ω _ g) (z.1 (toGS Ω _ h))
      rw [map_mul]
      exact hcoc _ _
    · rintro g ⟨hgK, A, hAl, hgA⟩
      show z.1 (toGS Ω _ g) = 0
      by_cases hAtop : A = ⊤
      · subst hAtop
        rw [(UpperTheory.V.Kum.placeDict ℚ Ω).1, Subgroup.mem_bot] at hgA
        rw [hgA, map_one, hz1]
      obtain ⟨v, hAv'⟩ := (UpperTheory.V.Kum.placeDict ℚ Ω).2.1 A hAtop
      by_cases hvS : v ∈ S
      · set w : S := ⟨v, hvS⟩
        have hne : w ≠ v0 := by
          intro hw
          apply hAl
          have h := (hAv' (l : 𝓞 ℚ)).mpr (by rw [show v = v0.1 from congrArg Subtype.val hw]; exact hlv0)
          simpa using h
        obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hAv w) hAv'
        rw [← hσ] at hgA
        have hgA' : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (Av w) := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hgA
        have hur := hL w hne (hmemv w)
        rw [H1ur, LinearMap.mem_ker] at hur
        have hur' := (Submodule.Quotient.mk_eq_zero _).mp hur
        rw [Submodule.mem_comap] at hur'
        obtain ⟨m, hm⟩ := hur'
        have hj := congrFun hm ⟨⟨σ⁻¹ * g * σ, Ine_le_Dec _ hgA'⟩, hgA'⟩
        rw [amitsur_d0_apply] at hj
        have hconj : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = 0 := by
          have hj' : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = ρ (toGS Ω _ (σ⁻¹ * g * σ)) m - m := hj.symm
          rw [hj']
          rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
            show ρ (toGS Ω _ g) (ρ (toGS Ω _ σ) m) = ρ (toGS Ω _ σ) m from hK g hgK _,
            ← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel, map_one, Module.End.one_apply, sub_self]
        set a := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ
        set b := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g
        have hb : ∀ m, ρ b m = m := hK g hgK
        rw [map_mul, map_mul, map_inv] at hconj
        have e1 := hcoc (a⁻¹ * b) a
        have e2 := hcoc a⁻¹ b
        have e3 := hcoc a⁻¹ a
        rw [inv_mul_cancel, hz1] at e3
        rw [map_mul, Module.End.mul_apply, hb, e2, hconj] at e1
        have hinv0 : ρ a⁻¹ (z.1 b) = 0 := by
          have : (0 : M) = ρ a⁻¹ (z.1 b) + (z.1 a⁻¹ + ρ a⁻¹ (z.1 a)) := by rw [e1]; abel
          rw [← e3, add_zero] at this
          exact this.symm
        have : z.1 b = ρ a (ρ a⁻¹ (z.1 b)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [this, hinv0, map_zero]
      · have hgN : g ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) :=
          Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
            (Set.mem_iUnion₂.mpr ⟨v, hvS, Set.mem_iUnion₂.mpr ⟨A, hAv', hgA⟩⟩))
        rw [show toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g = 1 from (QuotientGroup.eq_one_iff g).mpr hgN, hz1]
    · intro h hh
      exact hy ⟨h, hh⟩
  choose zc hzc using hex
  refine ⟨fun x => ⟨fun g => (zc x.1).1 (toGS Ω _ g), hA x.1 x.2 (zc x.1) (hzc x.1).1 (hzc x.1).2⟩, ?_⟩
  intro x x' hxx
  have hfun : (fun g => (zc x.1).1 (toGS Ω _ g)) = (fun g => (zc x'.1).1 (toGS Ω _ g)) :=
    congrArg Subtype.val hxx
  have hz : zc x.1 = zc x'.1 := by
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) q
    exact congrFun hfun g
  apply Subtype.ext
  rw [← (hzc x.1).1, ← (hzc x'.1).1, hz]
