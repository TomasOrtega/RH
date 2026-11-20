import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `N`. Use `(hf N).mul (hg N) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Conclude with `map_mul _ _ _`.
-/
private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R} (hf : AdicCont I f)
    (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  convert (hf N).mul (hg N) using 1
  funext x
  exact map_mul _ _ _

/- English proof (translation)
Introduce `N`. Establish `hJ : Ideal.map φ J ≤ I` using `Ideal.map_le_iff_le_comap.mpr (fun a ha => h a ha)`. Establish `hN : J ^ N ≤ Ideal.comap φ (I ^ N)`. Rewrite using `[← Ideal.map_le_iff_le_comap, Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hJ N`.

Use `(hf N).comp (Ideal.Quotient.lift (J ^ N) ((Ideal.Quotient.mk (I ^ N)).comp φ) (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hN ha)))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
private theorem ac_map {Γ O R : Type} [TopologicalSpace Γ] [CommRing O] [CommRing R] {J : Ideal O} {I : Ideal R} (φ : O →+* R)
    (h : ∀ a ∈ J, φ a ∈ I) {f : Γ → O} (hf : AdicCont J f) : AdicCont I fun x => φ (f x) := by
  intro N
  have hJ : Ideal.map φ J ≤ I := Ideal.map_le_iff_le_comap.mpr (fun a ha => h a ha)
  have hN : J ^ N ≤ Ideal.comap φ (I ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hJ N
  have := (hf N).comp (Ideal.Quotient.lift (J ^ N) ((Ideal.Quotient.mk (I ^ N)).comp φ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hN ha)))
  convert this using 1
  funext x
  simp

/- English proof (translation)
Establish `hset : {x | f x = y} = ⋂ N : ℕ, {x | Ideal.Quotient.mk (I ^ N) (f x) = Ideal.Quotient.mk (I ^ N) y}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `hx N`.

Rewrite using `[hx]`. Introduce `hx`. Rewrite using `[IsHausdorff.eq_iff_smodEq (I := I)]`. Introduce `N`. Simplify `Ideal.Quotient.eq.mp (hx N)` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`.

Rewrite using `[hset]`. Conclude with `isClosed_iInter fun N => ((hf N).isClopen_fiber _).isClosed`.
-/
private theorem ac_closed {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} [IsHausdorff I R] {f : Γ → R}
    (hf : AdicCont I f) (y : R) : IsClosed {x | f x = y} := by
  have hset : {x | f x = y} =
      ⋂ N : ℕ, {x | Ideal.Quotient.mk (I ^ N) (f x) = Ideal.Quotient.mk (I ^ N) y} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro hx N
      rw [hx]
    · intro hx
      rw [IsHausdorff.eq_iff_smodEq (I := I)]
      intro N
      simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using Ideal.Quotient.eq.mp (hx N)
  rw [hset]
  exact isClosed_iInter fun N => ((hf N).isClopen_fiber _).isClosed

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T c' h K R _ _ Q I _ hI hpair hcont`. Set `σ : G T.L Ω →* M4 R` to `{ toFun := fun g => algebraMap c'.O R (K.κ g : c'.O) • Q.r (resLe T.F_le g) map_one' := by simp map_mul' := fun a b => by`. Simplify using `only [map_mul, Units.val_mul, smul_mul_smul_comm] }`. Set `ρ' : G T.L Ω →* GL (Fin 4) R` to `σ.toHomUnits`. Establish `hρ' : ∀ g, ((ρ' g : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = σ g` using `fun g => rfl`.

Establish `hent : ∀ a b, AdicCont I fun g => σ g a b`. Introduce `a b`. Establish `h1 : AdicCont I fun g : G T.L Ω => algebraMap c'.O R (K.κ g : c'.O)` using `ac_map (algebraMap c'.O R) hI K.κ_cont`. Establish `h2 : AdicCont I fun g : G T.L Ω => Q.r (resLe T.F_le g) a b`. Introduce `N`.

Conclude with `(hcont a b N).comp_continuous (P1.towerGal D T).2.2.1`. Conclude with `ac_mul h1 h2`. Establish `hker : K.V.pr.ker ≤ ρ'.ker`. Apply `(phiKer K.V).2.2 ρ'.ker` to reduce the goal to its premises. Establish `hset : (ρ'.ker : Set (G T.L Ω)) = ⋂ a, ⋂ b, {g | σ g a b = (1 : Matrix (Fin 4) (Fin 4) R) a b}`.

Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]`. Rewrite using `[← Units.val_eq_one, hρ']`. Conclude with `⟨fun hg a b => by rw [hg], fun hg => Matrix.ext hg⟩`. Rewrite using `[hset]`.

Conclude with `isClosed_iInter fun a => isClosed_iInter fun b => ac_closed (hent a b) _`. Introduce `A v hAv hv g hg`. Rewrite `hv` using `[K.hV]`. Take `⟨hκ, hr⟩` from `K.unr A v hAv hv g hg`. Establish `hl : ¬ A.valuation (l : Ω) < 1`.

Introduce `hlt`. Apply `hv` to reduce the goal to its premises. Use `left`. Establish `hmem` using `(hAv (l : 𝓞 (W.Lp T.L))).mp (by simpa using hlt)`. Simplify using `using hmem`.

Establish `hN : resLe T.F_le g ∈ (T.fr ∅).N`. Express the relevant statement in the definitionally equal form `∃ A', Raw.Away (insert l ∅) A' ∧ resLe T.F_le g ∈ Ine A' ∧ D.rbar ((resQ T.F) (resLe T.F_le g)) = 1`. Use `⟨A, ?_, ((P1.towerGal D T).2.2.2.2.2 A g).2.mpr hg, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Simplify using `at hp`.

Substitute `hp` using the available equality. Conclude with `hl`. Rewrite using `[((P1.towerGal D T).2.2.2.2.1 g).1]`. Conclude with `hr`. Rewrite using `[MonoidHom.mem_ker, ← Units.val_eq_one, hρ']`.

Use `show algebraMap c'.O R (K.κ g : c'.O) • Q.r (resLe T.F_le g) = 1`. Rewrite using `[hκ, hpair.kill _ hN]`. Simplify using the standard rewrite rules. Set `e` to `QuotientGroup.quotientKerEquivOfSurjective K.V.pr (phiKer K.V).1`. Set `ρ : K.V.frame.G₀ →* GL (Fin 4) R` to `(QuotientGroup.lift K.V.pr.ker ρ' hker).comp e.symm.toMonoidHom`.

Establish `hρ : ∀ g, ρ (K.V.pr g) = ρ' g`. Introduce `g`. Establish `he : e.symm (K.V.pr g) = (g : G T.L Ω ⧸ K.V.pr.ker)`. Rewrite using `[MulEquiv.symm_apply_eq]`. Both sides reduce to the same expression.

Use `show QuotientGroup.lift K.V.pr.ker ρ' hker (e.symm (K.V.pr g)) = ρ' g`. Rewrite using `[he]`. Both sides reduce to the same expression. Establish `hmat : ∀ g, W.mat ρ (K.V.pr g) = σ g`. Introduce `g`.

Use `show ((ρ (K.V.pr g) : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = σ g`. Rewrite using `[hρ, hρ']`. Use `⟨ρ, fun g => ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[hmat]`. Both sides reduce to the same expression.

Introduce `N`. Establish `hq` using `(phiKer K.V).2.1`. Establish `heq : (fun x => Ideal.Quotient.mk (I ^ N) (W.mat ρ x a b)) ∘ K.V.pr = fun g => Ideal.Quotient.mk (I ^ N) (σ g a b)`. Use function extensionality and compare the values at `g`. Use `show Ideal.Quotient.mk (I ^ N) (W.mat ρ (K.V.pr g) a b) = _`.

Rewrite using `[hmat]`. Introduce `s`. Establish `hopen` using `hent a b N s`. Rewrite `hopen` using `[← heq]`. Conclude with `hq.isOpen_preimage.mp hopen`.
-/
theorem UpperTheory.V.Ws.P1.rhoEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (R : Type) [CommRing R] [Algebra c'.O R] (Q : PD T.ι (G T.F Ω) R) (I : Ideal R) [IsHausdorff I R], (∀ a ∈ maximalIdeal c'.O, algebraMap c'.O R a ∈ I) → (T.fr ∅).IsPair ((algebraMap c'.O R).comp (inc h)) Q → Q.Cont I →
          ∃ ρ : K.V.frame.G₀ →* GL (Fin 4) R, K.IsRho ρ Q ∧ ∀ a b, AdicCont I fun g => W.mat ρ g a b := by
  intro Ω _ _ _ l _ c D T c' h K R _ _ Q I _ hI hpair hcont
  let σ : G T.L Ω →* M4 R :=
    { toFun := fun g => algebraMap c'.O R (K.κ g : c'.O) • Q.r (resLe T.F_le g)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, Units.val_mul, smul_mul_smul_comm] }
  let ρ' : G T.L Ω →* GL (Fin 4) R := σ.toHomUnits
  have hρ' : ∀ g, ((ρ' g : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = σ g := fun g => rfl
  have hent : ∀ a b, AdicCont I fun g => σ g a b := by
    intro a b
    have h1 : AdicCont I fun g : G T.L Ω => algebraMap c'.O R (K.κ g : c'.O) :=
      ac_map (algebraMap c'.O R) hI K.κ_cont
    have h2 : AdicCont I fun g : G T.L Ω => Q.r (resLe T.F_le g) a b := by
      intro N
      exact (hcont a b N).comp_continuous (P1.towerGal D T).2.2.1
    exact ac_mul h1 h2
  have hker : K.V.pr.ker ≤ ρ'.ker := by
    apply (phiKer K.V).2.2 ρ'.ker
    · have hset : (ρ'.ker : Set (G T.L Ω)) =
          ⋂ a, ⋂ b, {g | σ g a b = (1 : Matrix (Fin 4) (Fin 4) R) a b} := by
        ext g
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
        rw [← Units.val_eq_one, hρ']
        exact ⟨fun hg a b => by rw [hg], fun hg => Matrix.ext hg⟩
      rw [hset]
      exact isClosed_iInter fun a => isClosed_iInter fun b => ac_closed (hent a b) _
    · intro A v hAv hv g hg
      rw [K.hV] at hv
      obtain ⟨hκ, hr⟩ := K.unr A v hAv hv g hg
      have hl : ¬ A.valuation (l : Ω) < 1 := by
        intro hlt
        apply hv
        left
        have hmem := (hAv (l : 𝓞 (W.Lp T.L))).mp (by simpa using hlt)
        simpa using hmem
      have hN : resLe T.F_le g ∈ (T.fr ∅).N := by
        change ∃ A', Raw.Away (insert l ∅) A' ∧ resLe T.F_le g ∈ Ine A' ∧
          D.rbar ((resQ T.F) (resLe T.F_le g)) = 1
        refine ⟨A, ?_, ((P1.towerGal D T).2.2.2.2.2 A g).2.mpr hg, ?_⟩
        · intro p hp
          simp at hp
          subst hp
          exact hl
        · rw [((P1.towerGal D T).2.2.2.2.1 g).1]
          exact hr
      rw [MonoidHom.mem_ker, ← Units.val_eq_one, hρ']
      show algebraMap c'.O R (K.κ g : c'.O) • Q.r (resLe T.F_le g) = 1
      rw [hκ, hpair.kill _ hN]
      simp
  let e := QuotientGroup.quotientKerEquivOfSurjective K.V.pr (phiKer K.V).1
  let ρ : K.V.frame.G₀ →* GL (Fin 4) R :=
    (QuotientGroup.lift K.V.pr.ker ρ' hker).comp e.symm.toMonoidHom
  have hρ : ∀ g, ρ (K.V.pr g) = ρ' g := by
    intro g
    have he : e.symm (K.V.pr g) = (g : G T.L Ω ⧸ K.V.pr.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift K.V.pr.ker ρ' hker (e.symm (K.V.pr g)) = ρ' g
    rw [he]
    rfl
  have hmat : ∀ g, W.mat ρ (K.V.pr g) = σ g := by
    intro g
    show ((ρ (K.V.pr g) : GL (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) = σ g
    rw [hρ, hρ']
  refine ⟨ρ, fun g => ?_, fun a b => ?_⟩
  · rw [hmat]
    rfl
  · intro N
    have hq := (phiKer K.V).2.1
    have heq : (fun x => Ideal.Quotient.mk (I ^ N) (W.mat ρ x a b)) ∘ K.V.pr =
        fun g => Ideal.Quotient.mk (I ^ N) (σ g a b) := by
      funext g
      show Ideal.Quotient.mk (I ^ N) (W.mat ρ (K.V.pr g) a b) = _
      rw [hmat]
    intro s
    have hopen := hent a b N s
    rw [← heq] at hopen
    exact hq.isOpen_preimage.mp hopen
