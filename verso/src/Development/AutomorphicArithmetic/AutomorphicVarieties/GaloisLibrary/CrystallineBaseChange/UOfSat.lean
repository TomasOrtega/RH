import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Sd Matrix GlobalTheory.LFun Formalism.UG

/- English proof (translation)
Establish `hfin : (MulAction.orbit K (a : G ⧸ K)).Finite` using `hf.subset fun c hc => by`. Rewrite using `[Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero`. Use `letI := hfin.fintype`. Rewrite using `[Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype, finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations.

Distinguish the cases in `hc : c ∈ MulAction.orbit K (a : G ⧸ K)`. Rewrite using `[h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]`. Rewrite using `[h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]`.
-/
private theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (a : G) (h : G → ℂ) (h1 : ∀ g : G, (g : G ⧸ K) ∈ MulAction.orbit K (a : G ⧸ K) → h g = 1)
    (h2 : ∀ g : G, (g : G ⧸ K) ∉ MulAction.orbit K (a : G ⧸ K) → h g = 0) (hf : {c : G ⧸ K | h c.out ≠ 0}.Finite) (x : V) :
    heckeVec ρ K h x = Hi.dc ρ K K a x := by
  classical
  have hfin : (MulAction.orbit K (a : G ⧸ K)).Finite := hf.subset fun c hc => by
    rw [Set.mem_setOf_eq, h1 _ (by rwa [QuotientGroup.out_eq'])]; exact one_ne_zero
  letI := hfin.fintype
  rw [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← finsum_eq_sum_of_fintype,
    finsum_set_coe_eq_finsum_mem (f := fun c : G ⧸ K => ρ c.out x), heckeVec]
  refine finsum_congr fun c => ?_
  by_cases hc : c ∈ MulAction.orbit K (a : G ⧸ K)
  · rw [h1 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]
  · rw [h2 _ (by rwa [QuotientGroup.out_eq'])]; simp [hc]

variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use extensionality with `g`. Use `⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩` and prove the remaining obligations. Use `haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)`. Conclude with `Subsingleton.elim _ _`.
-/
private theorem iwahori_level_zero_eq : K1 w 0 = KGL w 2 := by
  ext g
  refine ⟨fun ⟨k, _, e⟩ => ⟨k, e⟩, fun ⟨k, e⟩ => ⟨k, ?_, e⟩⟩
  haveI : Subsingleton (w.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ 0) :=
    Ideal.Quotient.subsingleton_iff.2 (by simp)
  exact Subsingleton.elim _ _

/- English proof (translation)
Use `hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_) (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x` and prove the remaining obligations. Take `⟨k, hk⟩` from `hg`. Establish `h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w 2` using `QuotientGroup.eq.1 hk`. Rewrite using `[Tj, Set.indicator_of_mem, Pi.one_apply]`. Use `⟨k, k.2, _, h, ?_⟩` and prove the remaining obligations.

Rewrite using `[← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]`. Rewrite using `[Tj, Set.indicator_of_notMem]`. Introduce and unpack `⟨k, hk, k', hk', e⟩`. Use `hg ⟨⟨k, hk⟩, ?_⟩` and prove the remaining obligations. Rewrite `e` using `[← ha, ← Units.val_mul, ← Units.val_mul]`.

Rewrite using `[Units.ext e]`. Conclude with `(QuotientGroup.mk_mul_of_mem (k * a) hk').symm`.
-/
private theorem hecke_Tj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) (w.adicCompletion F)) V)
    (j : ℕ) (a : GL (Fin 2) (w.adicCompletion F)) (ha : a.val = diagJ 2 (atFin w (unif w) : w.adicCompletion F) j) (x : V) :
    heckeVec ρ (KGL w 2) (Tj ℂ 2 (Ov F w) (atFin w (unif w) : w.adicCompletion F) j) x = Hi.dc ρ (KGL w 2) (KGL w 2) a x := by
  refine hecke_eq_dc ρ _ a _ (fun g hg => ?_) (fun g hg => ?_)
    (Formalism.UG.P.finite_support_cosets (Final.GLintComm F w 2) (Tj_mem_hecke (unif_spec w) j).2) x
  · obtain ⟨k, hk⟩ := hg
    have h : ((k : GL (Fin 2) (w.adicCompletion F)) * a)⁻¹ * g ∈ KGL w 2 := QuotientGroup.eq.1 hk
    rw [Tj, Set.indicator_of_mem, Pi.one_apply]
    refine ⟨k, k.2, _, h, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_left]
  · rw [Tj, Set.indicator_of_notMem]
    rintro ⟨k, hk, k', hk', e⟩
    refine hg ⟨⟨k, hk⟩, ?_⟩
    rw [← ha, ← Units.val_mul, ← Units.val_mul] at e
    rw [Units.ext e]
    exact (QuotientGroup.mk_mul_of_mem (k * a) hk').symm

/- English proof (translation)
Introduce `F _ _ w V _ _ ρ x α β ⟨_, hx', _, h⟩`. Establish `hx` using `GlobalTheory.LGrp.mem_fixed.1 hx'`. Prove the components needed by the constructor for the conclusion. Establish `h1` using `h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 1 (by norm_num)`. Apply the tactic sequence `rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]), h1]`.

Use `congr 1`. Rewrite using `[Complex.ofReal_cpow (by positivity)]`. Establish `: qV F w = normV w` using `rfl`. Simplify using `[satEig, Multiset.esymm, Multiset.powersetCard_one, this]`. Evaluate the numerical expressions using `[add_comm]`.

Establish `h2` using `h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 2 (by norm_num) set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))`. Apply the tactic sequence `rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2`. Establish `ho : ∀ q ∈ MulAction.orbit (KGL w 2) (z : _ ⧸ KGL w 2), q = z`. Introduce and unpack `_ ⟨k, rfl⟩`. Express the relevant statement in the definitionally equal form `(((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w 2) = _`.

Rewrite using `[← GlobalTheory.CuspRep.scalar_comm]`. Conclude with `QuotientGroup.mk_mul_of_mem _ k.2`. Rewrite `h2` using `[(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z} (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _) (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x hx, Finset.sum_single …`. Rewrite using `[h2]`. Simplify using `[satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]`.
-/
theorem UpperTheory.V.Br.uOfSat :
    UpperTheory.V.Br.UOfSat := by
  intro F _ _ w V _ _ ρ x α β ⟨_, hx', _, h⟩
  have hx := GlobalTheory.LGrp.mem_fixed.1 hx'
  constructor
  · have h1 := h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 1 (by norm_num)
    rw [Uop, iwahori_level_zero_eq, ← hecke_Tj w ρ 1 _ (by ext i j; fin_cases i <;> fin_cases j <;> simp [aff, diagJ]), h1]
    congr 1
    rw [Complex.ofReal_cpow (by positivity)]
    have : qV F w = normV w := rfl
    simp [satEig, Multiset.esymm, Multiset.powersetCard_one, this]
    norm_num [add_comm]
  · have h2 := h (atFin w (unif w) : w.adicCompletion F) (unif_spec w) 2 (by norm_num)
    set z := GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))
    rw [hecke_Tj w ρ 2 z (by ext i j; fin_cases i <;> fin_cases j <;> simp [z, diagJ])] at h2
    have ho : ∀ q ∈ MulAction.orbit (KGL w 2) (z : _ ⧸ KGL w 2), q = z := by
      rintro _ ⟨k, rfl⟩
      change (((k : GL (Fin 2) (w.adicCompletion F)) * z : GL (Fin 2) (w.adicCompletion F)) : _ ⧸ KGL w 2) = _
      rw [← GlobalTheory.CuspRep.scalar_comm]
      exact QuotientGroup.mk_mul_of_mem _ k.2
    rw [(Hi.dcSum ℂ _ V ρ _ _ z ((Set.finite_singleton _).subset ho)).1 {z}
      (fun y hy => by rw [Finset.mem_singleton.1 hy]; exact MulAction.mem_orbit_self _)
      (fun q hq => ⟨z, ⟨Finset.mem_singleton_self _, (ho q hq).symm⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩) x
      hx, Finset.sum_singleton] at h2
    rw [h2]
    simp [satEig, Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one]
