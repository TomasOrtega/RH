import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

section

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/- English proof (translation)
Establish `hc : IsClosed (φ.ker : Set Γ)`. Establish `: (φ.ker : Set Γ) = {g | φ g = 1}` using `rfl`. Rewrite using `[this]`. Conclude with `(h.isClopen_fiber 1).isClosed`. Conclude with `Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.2 (hN g hg)) hc`.
-/
private theorem le_ker [IsTopologicalGroup Γ] {G : Type} [Monoid G] (φ : Γ →* G) (h : IsLocallyConstant φ)
    (N : Set Γ) (hN : ∀ g ∈ N, φ g = 1) : (Subgroup.normalClosure N).topologicalClosure ≤ φ.ker := by
  have hc : IsClosed (φ.ker : Set Γ) := by
    have : (φ.ker : Set Γ) = {g | φ g = 1} := rfl
    rw [this]
    exact (h.isClopen_fiber 1).isClosed
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.2 (hN g hg)) hc

/- English proof (translation)
Introduce `s` and use `(QuotientGroup.isQuotientMap_mk M).isOpen_preimage.1 (h s)`.
-/
private theorem lc_quot {Y : Type} (M : Subgroup Γ) (f : Γ ⧸ M → Y)
    (h : IsLocallyConstant fun g : Γ => f (QuotientGroup.mk g)) : IsLocallyConstant f := fun s =>
  (QuotientGroup.isQuotientMap_mk M).isOpen_preimage.1 (h s)

/- English proof (translation)
Introduce `H hH`. Establish `hc : Continuous (QuotientGroup.mk' M)` using `QuotientGroup.continuous_mk`. Use `haveI := h (H.comap (QuotientGroup.mk' M)) (hH.preimage hc) fun g hg => by`. Rewrite using `[Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]`. Conclude with `H.one_mem`.

Set `π` to `(QuotientGroup.mk' M).subgroupComap H`. Establish `hπ : Continuous π` using `(hc.comp continuous_subtype_val).subtype_mk _`. Establish `hs : Function.Surjective π` using `(QuotientGroup.mk' M).subgroupComap_surjective_of_surjective H (QuotientGroup.mk'_surjective M)`. Use `Finite.of_injective (β := {φ : H.comap (QuotientGroup.mk' M) →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set (H.comap (QuotientGroup.mk' M))) ∧ ∀ g : H.comap (QuotientGroup.mk' M), (g : Γ) ∈ M → φ g = 1}) (fun φ => ⟨φ.1.comp π, φ.2.preimage hπ, fun g hg => ?_⟩) fun φ φ' e => ?_` and prove the remaining obligations. Establish `: π g = 1` using `Subtype.ext ((QuotientGroup.eq_one_iff (g : Γ)).2 hg)`.

Rewrite using `[MonoidHom.comp_apply, this, map_one]`. Conclude with `Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))`.
-/
private theorem phi_quot (l : ℕ) (M : Subgroup Γ) [M.Normal]
    (h : ∀ H : Subgroup Γ, IsOpen (H : Set Γ) → M ≤ H →
      Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : Γ) ∈ M → φ g = 1}) :
    PhiCond (Γ ⧸ M) l := by
  intro H hH
  have hc : Continuous (QuotientGroup.mk' M) := QuotientGroup.continuous_mk
  haveI := h (H.comap (QuotientGroup.mk' M)) (hH.preimage hc) fun g hg => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
    exact H.one_mem
  let π := (QuotientGroup.mk' M).subgroupComap H
  have hπ : Continuous π := (hc.comp continuous_subtype_val).subtype_mk _
  have hs : Function.Surjective π :=
    (QuotientGroup.mk' M).subgroupComap_surjective_of_surjective H (QuotientGroup.mk'_surjective M)
  refine Finite.of_injective (β := {φ : H.comap (QuotientGroup.mk' M) →* Multiplicative (ZMod l) //
      IsOpen (φ.ker : Set (H.comap (QuotientGroup.mk' M))) ∧
        ∀ g : H.comap (QuotientGroup.mk' M), (g : Γ) ∈ M → φ g = 1})
    (fun φ => ⟨φ.1.comp π, φ.2.preimage hπ, fun g hg => ?_⟩) fun φ φ' e => ?_
  · have : π g = 1 := Subtype.ext ((QuotientGroup.eq_one_iff (g : Γ)).2 hg)
    rw [MonoidHom.comp_apply, this, map_one]
  · exact Subtype.ext ((MonoidHom.cancel_right hs).1 (congrArg Subtype.val e))

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
  {rbar : Γ →* Matrix ι ι (ResidueField Λ)}

/- English proof (translation)
Establish `key : ∀ x y : R, (∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) x = Ideal.Quotient.mk _ y) → x = y`. Introduce `x y hxy`. Establish `hH : IsHausdorff (maximalIdeal R) R` using `(IsCO.complete (O := Λ)).toIsHausdorff`. Rewrite using `[← sub_eq_zero]`. Apply `hH.haus` to reduce the goal to its premises.

Introduce `n`. Rewrite using `[SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]`. Conclude with `Ideal.Quotient.eq.1 (hxy n)`. Establish `hc : IsClosed (s.hom.ker : Set Γ)`. Establish `: (s.hom.ker : Set Γ) = ⋂ a, ⋂ b, ⋂ n : ℕ, {g | Ideal.Quotient.mk (maximalIdeal R ^ n) (s.hom g a b) = Ideal.Quotient.mk (maximalIdeal R ^ n) ((1 : Matrix ι ι R) a b)}`.

Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `hg a b n`. Rewrite using `[hg]`.

Introduce `hg`. Use extensionality with `a b`. Conclude with `key _ _ (hg a b)`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun n => ((s.cont a b n).isClopen_fiber _).isClosed`.

Conclude with `Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.2 (hN g hg)) hc`.
-/
private theorem kills_closure [IsTopologicalGroup Γ] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    (s : Lift Λ rbar R) (N : Set Γ) (hN : ∀ g ∈ N, s.hom g = 1) :
    (Subgroup.normalClosure N).topologicalClosure ≤ s.hom.ker := by
  have key : ∀ x y : R, (∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) x = Ideal.Quotient.mk _ y) → x = y := by
    intro x y hxy
    have hH : IsHausdorff (maximalIdeal R) R := (IsCO.complete (O := Λ)).toIsHausdorff
    rw [← sub_eq_zero]
    apply hH.haus
    intro n
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact Ideal.Quotient.eq.1 (hxy n)
  have hc : IsClosed (s.hom.ker : Set Γ) := by
    have : (s.hom.ker : Set Γ) = ⋂ a, ⋂ b, ⋂ n : ℕ,
        {g | Ideal.Quotient.mk (maximalIdeal R ^ n) (s.hom g a b) =
          Ideal.Quotient.mk (maximalIdeal R ^ n) ((1 : Matrix ι ι R) a b)} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro hg a b n
        rw [hg]
      · intro hg
        ext a b
        exact key _ _ (hg a b)
    rw [this]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun n =>
      ((s.cont a b n).isClopen_fiber _).isClosed
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.2 (hN g hg)) hc

end

/- English proof (translation)
Introduce `l _ Λ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ _ rbar N hfin hloc hN`. Use `haveI : (Subgroup.normalClosure N).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _`. Establish `hKc : IsClosed ((Subgroup.normalClosure N).topologicalClosure : Set Γ)` using `Subgroup.isClosed_topologicalClosure _`. Use `haveI : TotallyDisconnectedSpace (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) := (UpperTheory.V.AlgebraTools.totallyDisconnected_quot Γ _ hKc).1`. Establish `hK : (Subgroup.normalClosure N).topologicalClosure ≤ rbar.ker` using `le_ker rbar hloc N hN`.

Set `rq : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure →* Matrix ι ι (ResidueField Λ)` to `QuotientGroup.lift _ rbar hK`. Establish `hlq : IsLocallyConstant rq` using `lc_quot _ rq hloc`. Establish `hΦ : PhiCond (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) l` using `phi_quot l _ fun H hH hKH => hfin H hH (le_trans (Subgroup.le_topologicalClosure _) hKH)`. Take `⟨R, _, _, _, r0, hr0⟩` from `univ_lift l Λ (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) ι rq hΦ hlq`. Set `r : Lift Λ rbar R` to `⟨r0.hom.comp (QuotientGroup.mk' _), fun a b n => (r0.cont a b n).comp_continuous continuous_quot_mk, fun g a b => r0.red (g : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b⟩`.

Use `⟨R, inferInstance, inferInstance, inferInstance, r, ?_⟩` and prove the remaining obligations. Introduce `R' _ _ _`. Prove the components needed by the constructor for the conclusion. Introduce `f n hn`. Establish `h1 : ((n : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure)) = 1` using `(QuotientGroup.eq_one_iff n).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hn))`.

Use extensionality with `a b`. Rewrite using `[Lift.map_hom]`. Use `show f (r0.hom (n : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b) = _`. Rewrite using `[h1, map_one]`. Apply the tactic sequence `by_cases hab : a = b <;> simp [Matrix.one_apply, hab]`.

Introduce `r' hr'`. Establish `hK' : (Subgroup.normalClosure N).topologicalClosure ≤ r'.hom.ker` using `kills_closure r' N hr'`. Set `rq' : Lift Λ rq R'` to `⟨QuotientGroup.lift _ r'.hom hK', fun a b n => lc_quot _ _ (r'.cont a b n), fun q a b => by`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H g => exact r'.red g a b⟩`.

Take `⟨f, hf, huniq⟩` from `(hr0 R').2 rq' trivial`. Establish `key : ∀ g : R →ₐ[Λ] R', Lift.map g r = r' ↔ Lift.map g r0 = rq'`. Introduce `g`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Apply `Lift.ext` to reduce the goal to its premises. Use `MonoidHom.ext fun q => ?_` and prove the remaining obligations. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H x`. Use extensionality with `a b`.

Use `congrArg (fun y : Lift Λ rbar R' => y.hom x a b) h` as an intermediate fact. Conclude with `(Lift.map_hom g r0 _ a b).trans ((Lift.map_hom g r x a b).symm.trans this)`. Introduce `h`. Apply `Lift.ext` to reduce the goal to its premises. Use `MonoidHom.ext fun x => ?_` and prove the remaining obligations.

Use extensionality with `a b`. Use `congrArg (fun y : Lift Λ rq R' => y.hom (x : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b) h` as an intermediate fact. Conclude with `(Lift.map_hom g r x a b).trans ((Lift.map_hom g r0 _ a b).symm.trans this)`. Conclude with `⟨f, (key f).2 hf, fun g hg => huniq g ((key g).1 hg)⟩`.
-/
theorem UpperTheory.V.Ws.sxUnivKill :
    ∀ (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] [CharP (ResidueField Λ) l] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField Λ)) (N : Set Γ), (∀ H : Subgroup Γ, IsOpen (H : Set Γ) → Subgroup.normalClosure N ≤ H → Finite {φ : H →* Multiplicative (ZMod l) // IsOpen (φ.ker : Set H) ∧ ∀ g : H, (g : Γ) ∈ (Subgroup.normalClosure N).topologicalClosure → φ g = 1}) → IsLocallyConstant rbar → (∀ n ∈ N, rbar n = 1) → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (r : Lift Λ rbar R), Represents (killCond rbar N) r := by
  intro l _ Λ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ _ rbar N hfin hloc hN
  haveI : (Subgroup.normalClosure N).topologicalClosure.Normal := Subgroup.is_normal_topologicalClosure _
  have hKc : IsClosed ((Subgroup.normalClosure N).topologicalClosure : Set Γ) :=
    Subgroup.isClosed_topologicalClosure _
  haveI : TotallyDisconnectedSpace (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) :=
    (UpperTheory.V.AlgebraTools.totallyDisconnected_quot Γ _ hKc).1
  have hK : (Subgroup.normalClosure N).topologicalClosure ≤ rbar.ker := le_ker rbar hloc N hN
  let rq : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure →* Matrix ι ι (ResidueField Λ) :=
    QuotientGroup.lift _ rbar hK
  have hlq : IsLocallyConstant rq := lc_quot _ rq hloc
  have hΦ : PhiCond (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) l :=
    phi_quot l _ fun H hH hKH => hfin H hH (le_trans (Subgroup.le_topologicalClosure _) hKH)
  obtain ⟨R, _, _, _, r0, hr0⟩ := univ_lift l Λ (Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) ι rq hΦ hlq
  let r : Lift Λ rbar R :=
    ⟨r0.hom.comp (QuotientGroup.mk' _), fun a b n => (r0.cont a b n).comp_continuous continuous_quot_mk,
      fun g a b => r0.red (g : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b⟩
  refine ⟨R, inferInstance, inferInstance, inferInstance, r, ?_⟩
  intro R' _ _ _
  constructor
  · intro f n hn
    have h1 : ((n : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure)) = 1 :=
      (QuotientGroup.eq_one_iff n).2 (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hn))
    ext a b
    rw [Lift.map_hom]
    show f (r0.hom (n : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b) = _
    rw [h1, map_one]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  · intro r' hr'
    have hK' : (Subgroup.normalClosure N).topologicalClosure ≤ r'.hom.ker := kills_closure r' N hr'
    let rq' : Lift Λ rq R' :=
      ⟨QuotientGroup.lift _ r'.hom hK', fun a b n => lc_quot _ _ (r'.cont a b n), fun q a b => by
        induction q using QuotientGroup.induction_on with
        | H g => exact r'.red g a b⟩
    obtain ⟨f, hf, huniq⟩ := (hr0 R').2 rq' trivial
    have key : ∀ g : R →ₐ[Λ] R', Lift.map g r = r' ↔ Lift.map g r0 = rq' := by
      intro g
      constructor
      · intro h
        apply Lift.ext
        refine MonoidHom.ext fun q => ?_
        induction q using QuotientGroup.induction_on with
        | H x =>
          ext a b
          have := congrArg (fun y : Lift Λ rbar R' => y.hom x a b) h
          exact (Lift.map_hom g r0 _ a b).trans ((Lift.map_hom g r x a b).symm.trans this)
      · intro h
        apply Lift.ext
        refine MonoidHom.ext fun x => ?_
        ext a b
        have := congrArg (fun y : Lift Λ rq R' => y.hom (x : Γ ⧸ (Subgroup.normalClosure N).topologicalClosure) a b) h
        exact (Lift.map_hom g r x a b).trans ((Lift.map_hom g r0 _ a b).symm.trans this)
    exact ⟨f, (key f).2 hf, fun g hg => huniq g ((key g).1 hg)⟩
