import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.UnivQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RamFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

namespace UpperTheory.V.U3

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

/- English proof (translation)
Establish `h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H)`. Rewrite using `[QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']`. Simplify `QuotientGroup.eq.1 h` using `[mul_assoc]`.
-/
private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

/- English proof (translation)
Introduce `H hH`. Use `haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH`. Use `haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete`. Use `letI : TopologicalSpace (ZMod n) := ⊥`. Use `haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩`.

Establish `hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x` using `fun x => continuous_inv.smul continuous_const`. Establish `hc : ContAction (permR (ZMod n) H)`. Use `continuous_pi fun x => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2` using `continuous_of_discreteTopology`. Conclude with `h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))`.

Use `haveI h1 := h _ _ hc`. Use `haveI : Finite (Z1 (permR (ZMod n) H)) := by`. Establish `hB : Finite (B1 (permR (ZMod n) H))` using `(Set.finite_range _).to_subtype`. Establish `hB' : Finite ((B1 (permR (ZMod n) H)).comap (Z1 (permR (ZMod n) H)).subtype).toAddSubgroup` using `Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permR (ZMod n) H))) fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))`. Conclude with `@Finite.of_addSubgroup_quotient _ _ _ hB' h1`.

Establish `hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ` using `fun φ hφ => continuous_of_continuousAt_one φ (by`. Rewrite using `[ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]`. Conclude with `hφ.mem_nhds φ.ker.one_mem)`. Set `c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → Z1 (permR (ZMod n) H)` to `fun φ => ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by`. Use `⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩` and prove the remaining obligations.

Conclude with `(continuous_const.mul continuous_id).mul ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))`. Use function extensionality and compare the values at `x`. Rewrite using `[Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]`. Use `congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `[mul_smul, mul_assoc]⟩`.

Use `Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)` and prove the remaining obligations. Set `x : Γ ⧸ H` to `((1 : Γ) : Γ ⧸ H)`. Establish `hx : x.out ∈ H`. Use `QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm` as an intermediate fact. Simplify using `using this`.

Establish `hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x`. Express the relevant statement in the definitionally equal form `(((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)`. Rewrite using `[QuotientGroup.eq]`. Simplify using `using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)`. Establish `hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hfix]`. Use `group`. Use `congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x` as an intermediate fact. Simplify using `only [c, hu] at this`.

Conclude with `Multiplicative.toAdd.injective this`.
-/
private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x => continuous_inv.smul continuous_const
  have hc : ContAction (permR (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 := continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (Z1 (permR (ZMod n) H)) := by
    have hB : Finite (B1 (permR (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((B1 (permR (ZMod n) H)).comap (Z1 (permR (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permR (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ := fun φ hφ =>
    continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → Z1 (permR (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

/- English proof (translation)
Introduce `H hH` and use `by haveI := h (H.comap π) (hH.preimage hc) let p : H.comap π →* H := π.subgroupComap H have hp : Continuous p := (hc.comp continuous_subtype_val).subtype_mk _ have hs : Function.Surjective p := MonoidHom.subgroupComap_surjective_of_surjective _ _ hπ refine Finite.of_injective (β …`.
-/
private theorem phi_surj {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ'] (π : Γ →* Γ')
    (hc : Continuous π) (hπ : Function.Surjective π) {l : ℕ} (h : PhiCond Γ l) : PhiCond Γ' l := fun H hH => by
  haveI := h (H.comap π) (hH.preimage hc)
  let p : H.comap π →* H := π.subgroupComap H
  have hp : Continuous p := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective p := MonoidHom.subgroupComap_surjective_of_surjective _ _ hπ
  refine Finite.of_injective
    (β := {φ : H.comap π →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set (H.comap π))})
    (fun φ => ⟨φ.1.comp p, φ.2.preimage hp⟩) fun φ φ' e => ?_
  exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

/- English proof (translation)
Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Use `haveI hK : CompactSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := inferInstance`. Use `haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩`. Establish `key : PhiCond (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1)` using `phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by`. Take `⟨-, f1, -⟩` from `hGF ℚ Ω l 1 M S ρ one_pos hS hρ`.

Conclude with `f1`. Rewrite `key` using `[pow_one]`. Use `phi_surj (QuotientGroup.lift _ (QuotientGroup.mk' M) fun g hg => (QuotientGroup.eq_one_iff g).2 (hM hg)) ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 continuous_quotient_mk') (fun y => ?_) key` and prove the remaining obligations. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective y`. Conclude with `⟨QuotientGroup.mk g, rfl⟩`.
-/
private theorem phi_unr (hGF : GlobalFiniteness) {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [hl : Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ContainsAbove S l) (M : Subgroup (G ℚ Ω)) [M.Normal]
    (hM : NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) ≤ M) : PhiCond (G ℚ Ω ⧸ M) l := by
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hK : CompactSpace (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) := inferInstance
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) := phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
    obtain ⟨-, f1, -⟩ := hGF ℚ Ω l 1 M S ρ one_pos hS hρ
    exact f1
  rw [pow_one] at key
  refine phi_surj (QuotientGroup.lift _ (QuotientGroup.mk' M) fun g hg => (QuotientGroup.eq_one_iff g).2 (hM hg))
    ((QuotientGroup.isQuotientMap_mk _).continuous_iff.2 continuous_quotient_mk') (fun y => ?_) key
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk g, rfl⟩

end UpperTheory.V.U3

/- English proof (translation)
Introduce `hI Ω _ _ _ K _ _ _ l hl c N hN e ψ D U g₁ hg₁`. Use `haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω`. Take `⟨hc, hf, hlm, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Use `haveI := hc`. Use `haveI : Finite (ResidueField c.O) := hf`.

Use `haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by`. Rewrite using `[← map_natCast (residue c.O), residue_eq_zero_iff]`. Conclude with `hlm)`. Take `⟨-, -, -, hη, hΨ, hK, -, -, -, hKill, -⟩` from `dat_facts D`. Use `haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`.

Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩`. Take `⟨T, hT⟩` from `(ramFinite ℚ ℚ K Ω).1`. Take `⟨-, -, -, -, hIne⟩` from `Chr.clsFacts ℚ Ω N`. Establish `hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((l * N : ℕ) : 𝓞 ℚ)}}.Finite` using `Ideal.finite_factors (by simpa using ⟨hl.out.ne_zero, hN.out⟩)`.

Establish `hmem : ∀ v, ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ T ∪ hfin.toFinset` using `fun v hv => Finset.mem_union_right _ (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 hv))`. Establish `hval : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ∀ n : ℕ, A.valuation (n : Ω) < 1 → ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal`. Introduce `A v hv n hn`. Establish `h` using `hv ((n : ℕ) : 𝓞 ℚ)`. Establish `e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω)` using `by simp`.

Rewrite `h` using `[e]`. Conclude with `h.1 hn`. Use `haveI : (Subgroup.normalClosure D.Kill).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _`. Establish `hΦ : PhiCond (G ℚ Ω ⧸ (Subgroup.normalClosure D.Kill).topologicalClosure) l`. Use `phi_unr hI.gf l (T ∪ hfin.toFinset) (fun v hv => hmem v ?_) _ (Subgroup.topologicalClosure_mono (Subgroup.normalClosure_mono fun g hg => ?_))` and prove the remaining obligations.

Rewrite using `[Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hv`. Simplify using `only [Set.mem_iUnion] at hg`. Take `⟨v, hv, A, hA, hg⟩` from `hg`. Establish `hv' : ((l * N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal` using `fun h => hv (hmem v h)`.

Rewrite `hv'` using `[Nat.cast_mul]`. Use `(hKill g).2 ⟨A, fun h => hv' (v.asIdeal.mul_mem_right _ (hval A v hA l h)), hg, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← MonoidHom.mem_ker, D.η_ker]`. Conclude with `hT v (fun h => hv (Finset.mem_union_left _ h)) A hA ⟨by rw [galOf_self]; trivial, hg⟩`. Establish `h1 : Chr.cls ℚ Ω N g = 1` using `hIne A (fun h => hv' (v.asIdeal.mul_mem_left _ (hval A v hA N h))) hg`.

Simplify using `only [Chr.dirG, MonoidHom.comp_apply, h1, map_one]`. Conclude with `(exists_sRing D.ι_cont U (D.loc.It U) D.cc g₁ hg₁ (Loc.locGood hI.loc D.loc U) D.Ψ_cont hK (exists_univ l D.η D.Ψ hη hΨ D.Kill (fun g ⟨_, _, _, h⟩ => h) _ rfl hΦ)).2`.
-/
theorem UpperTheory.V.U3.exists_ring :
    CohInp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) (U : D.ULoc) (g₁ : G ℚ Ω), D.Marked g₁ → Nonempty (D.Ring U g₁) := by
  intro hI Ω _ _ _ K _ _ _ l hl c N hN e ψ D U g₁ hg₁
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨hc, hf, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI := hc
  haveI : Finite (ResidueField c.O) := hf
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  obtain ⟨-, -, -, hη, hΨ, hK, -, -, -, hKill, -⟩ := dat_facts D
  haveI : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsAlgClosure K Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  obtain ⟨T, hT⟩ := (ramFinite ℚ ℚ K Ω).1
  obtain ⟨-, -, -, -, hIne⟩ := Chr.clsFacts ℚ Ω N
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | v.asIdeal ∣ Ideal.span {((l * N : ℕ) : 𝓞 ℚ)}}.Finite :=
    Ideal.finite_factors (by simpa using ⟨hl.out.ne_zero, hN.out⟩)
  classical
  have hmem : ∀ v, ((l * N : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → v ∈ T ∪ hfin.toFinset := fun v hv =>
    Finset.mem_union_right _ (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 hv))
  have hval : ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v → ∀ n : ℕ,
      A.valuation (n : Ω) < 1 → ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    intro A v hv n hn
    have h := hv ((n : ℕ) : 𝓞 ℚ)
    have e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
    rw [e] at h
    exact h.1 hn
  haveI : (Subgroup.normalClosure D.Kill).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hΦ : PhiCond (G ℚ Ω ⧸ (Subgroup.normalClosure D.Kill).topologicalClosure) l := by
    refine phi_unr hI.gf l (T ∪ hfin.toFinset) (fun v hv => hmem v ?_) _
      (Subgroup.topologicalClosure_mono (Subgroup.normalClosure_mono fun g hg => ?_))
    · rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hv
    · simp only [Set.mem_iUnion] at hg
      obtain ⟨v, hv, A, hA, hg⟩ := hg
      have hv' : ((l * N : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun h => hv (hmem v h)
      rw [Nat.cast_mul] at hv'
      refine (hKill g).2 ⟨A, fun h => hv' (v.asIdeal.mul_mem_right _ (hval A v hA l h)), hg, ?_, ?_⟩
      · rw [← MonoidHom.mem_ker, D.η_ker]
        exact hT v (fun h => hv (Finset.mem_union_left _ h)) A hA ⟨by rw [galOf_self]; trivial, hg⟩
      · have h1 : Chr.cls ℚ Ω N g = 1 := hIne A (fun h => hv' (v.asIdeal.mul_mem_left _ (hval A v hA N h))) hg
        simp only [Chr.dirG, MonoidHom.comp_apply, h1, map_one]
  exact (exists_sRing D.ι_cont U (D.loc.It U) D.cc g₁ hg₁ (Loc.locGood hI.loc D.loc U) D.Ψ_cont hK
    (exists_univ l D.η D.Ψ hη hΨ D.Kill (fun g ⟨_, _, _, h⟩ => h) _ rfl hΦ)).2
