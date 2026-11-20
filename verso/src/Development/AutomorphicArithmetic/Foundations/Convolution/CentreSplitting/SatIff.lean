import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.FixedDense
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Establish `hS : (Function.support fun c : G ⧸ K => h c.out).Finite` using `Formalism.UG.P.finite_support_cosets hK hh.2`. Establish `hc : ∀ g, Continuous (ρ g)` using `fun g => (AddMonoidHomClass.isometry_of_norm (ρ g) (hρ g)).continuous`. Establish `e : (fun v => GlobalTheory.LFun.heckeVec ρ K h v) = fun v => ∑ c ∈ hS.toFinset, h c.out • ρ c.out v`. Use function extensionality and compare the values at `v`. Use `finsum_eq_sum_of_support_subset _ fun c hc' => ?_` and prove the remaining obligations.

Simplify using `only [Set.Finite.coe_toFinset, Function.mem_support]`. Conclude with `fun h0 => hc' (by simp [h0])`. Rewrite using `[e]`. Conclude with `continuous_finset_sum _ fun c _ => (hc _).const_smul _`.
-/
private theorem continuous_heckeVec {G H : Type} [Group G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {ρ : Representation ℂ G H} (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) {K : Subgroup G} (hK : Formalism.UG.IsCommensurated K)
    {h : G → ℂ} (hh : h ∈ Formalism.UG.Hecke ℂ K) : Continuous fun v => GlobalTheory.LFun.heckeVec ρ K h v := by
  have hS : (Function.support fun c : G ⧸ K => h c.out).Finite := Formalism.UG.P.finite_support_cosets hK hh.2
  have hc : ∀ g, Continuous (ρ g) := fun g => (AddMonoidHomClass.isometry_of_norm (ρ g) (hρ g)).continuous
  have e : (fun v => GlobalTheory.LFun.heckeVec ρ K h v) = fun v => ∑ c ∈ hS.toFinset, h c.out • ρ c.out v := by
    funext v
    refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    exact fun h0 => hc' (by simp [h0])
  rw [e]
  exact continuous_finset_sum _ fun c _ => (hc _).const_smul _

/- English proof (translation)
Introduce `E _ _ _ n μ _ π V h w B`. Take `⟨J, hi, hd, -, hJ'⟩` from `UpperTheory.ConvolutionTheory.Dp.locEmb E n μ π V h`. Establish `hJ` using `hJ' w`. Establish `hρ : ∀ g v, ‖locOn h.summand w g v‖ = ‖v‖` using `fun g v => by`. Express the relevant statement in the definitionally equal form `‖RG μ (finGL E n (locGL E n w g)) (v : LL μ)‖ = ‖(v : LL μ)‖`.

Conclude with `UnitaryRep.norm_map _ _ _`. Establish `hτ : ∀ x, IsOpen {g | π.locRep w g x = x}` using `fun x => by`. Take `⟨ψ, rfl⟩` from `(Cm.carrierEq π).surjective x`. Establish `h1` using `((Cm.isAdmissible_toModule π).1 ψ).preimage (CuspSub.continuous_locGL w)`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `g`. Establish `e : π.locRep w g (Cm.carrierEq π ψ) = Cm.carrierEq π ((Cm.toModule π).τ (locGL E n w g) ψ)`. Rewrite using `[CuspSub.locRep_eq, Cm.carrierEq_τ]`. Express the relevant statement in the definitionally equal form `π.locRep w g (Cm.carrierEq π ψ) = Cm.carrierEq π ψ ↔ (Cm.toModule π).τ (locGL E n w g) ψ = ψ`. Rewrite using `[e]`.

Conclude with `(Cm.carrierEq π).injective.eq_iff`. Establish `hK` using `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2`. Establish `hdense` using `UpperTheory.ConvolutionTheory.Dp.fixedDense _ _ _ (locOn h.summand w) (π.locRep w) J (GlobalTheory.LFun.KGL w n) hK hρ hτ hJ hd`. Establish `hcl : ∀ ϖ, Formalism.UG.IsUnifV E w ϖ → ∀ (j : ℕ) (c : ℂ), IsClosed {v : V | GlobalTheory.LFun.heckeVec (locOn h.summand w) (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) v = c • v}` using `fun ϖ hϖ j c => isClosed_eq (continuous_heckeVec hρ (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j)) (continuous_const_smul c)`. Express the relevant statement in the definitionally equal form `GlobalTheory.LFun.HasSatGL w (π.locRep w) B ↔ _`.

Prove the components needed by the constructor for the conclusion. Introduce `hB`. Use `⟨?_, fun v hv h0 => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hB.exists_vec`. Establish `h1` using `hx.map J hJ fun e => hx.1 (hi (by rw [e, map_zero]))`.

Conclude with `(Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩`. Use `⟨h0, hv, hB.card, fun ϖ hϖ j hj => ?_⟩` and prove the remaining obligations. Establish `hv'` using `hdense v fun u hu => GlobalTheory.LGrp.mem_fixed.1 hv u hu`. Use `closure_minimal ?_ (hcl ϖ hϖ j _) hv'` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Distinguish the cases in `hx0 : x = 0`. Substitute `hx0` using the available equality. Simplify using `[GlobalTheory.LFun.heckeVec]`. Conclude with `((hB.2 x (GlobalTheory.LGrp.mem_fixed.2 hx) hx0).map J hJ fun e => hx0 (hi (by rw [e, map_zero]))).2.2.2 ϖ hϖ j hj`. Introduce `hB`.

Take `⟨v, hv⟩` from `hB.exists_vec`. Establish `hv'` using `hdense v fun u hu => GlobalTheory.LGrp.mem_fixed.1 hv.2.1 u hu`. Use `⟨(Submodule.ne_bot_iff _).2 ?_, fun x hx h0 => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hno push_neg at hno`. Establish `hsub : J '' {x | ∀ u ∈ GlobalTheory.LFun.KGL w n, π.locRep w u x = x} ⊆ {0}`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite using `[hno x (GlobalTheory.LGrp.mem_fixed.2 hx), map_zero]`. Both sides reduce to the same expression. Conclude with `hv.1 (closure_minimal hsub isClosed_singleton hv')`. Establish `hJx : J x ∈ GlobalTheory.PRep.fixed (locOn h.summand w) (GlobalTheory.LFun.KGL w n)` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hJ, GlobalTheory.LGrp.mem_fixed.1 hx k hk]`.

Conclude with `GlobalTheory.LFun.IsSatVecGL.of_map J hJ hi (hB.2 _ hJx fun e => h0 (hi (by rw [e, map_zero])))`.
-/
theorem UpperTheory.ConvolutionTheory.Dp.satIff :
    UpperTheory.ConvolutionTheory.Dp.SatIff := by
  intro E _ _ _ n μ _ π V h w B
  obtain ⟨J, hi, hd, -, hJ'⟩ := UpperTheory.ConvolutionTheory.Dp.locEmb E n μ π V h
  have hJ := hJ' w
  have hρ : ∀ g v, ‖locOn h.summand w g v‖ = ‖v‖ := fun g v => by
    change ‖RG μ (finGL E n (locGL E n w g)) (v : LL μ)‖ = ‖(v : LL μ)‖
    exact UnitaryRep.norm_map _ _ _
  have hτ : ∀ x, IsOpen {g | π.locRep w g x = x} := fun x => by
    obtain ⟨ψ, rfl⟩ := (Cm.carrierEq π).surjective x
    have h1 := ((Cm.isAdmissible_toModule π).1 ψ).preimage (CuspSub.continuous_locGL w)
    convert h1 using 1
    ext g
    have e : π.locRep w g (Cm.carrierEq π ψ) = Cm.carrierEq π ((Cm.toModule π).τ (locGL E n w g) ψ) := by
      rw [CuspSub.locRep_eq, Cm.carrierEq_τ]
    change π.locRep w g (Cm.carrierEq π ψ) = Cm.carrierEq π ψ ↔ (Cm.toModule π).τ (locGL E n w g) ψ = ψ
    rw [e]
    exact (Cm.carrierEq π).injective.eq_iff
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have hdense := UpperTheory.ConvolutionTheory.Dp.fixedDense _ _ _ (locOn h.summand w) (π.locRep w) J (GlobalTheory.LFun.KGL w n) hK hρ hτ hJ hd
  have hcl : ∀ ϖ, Formalism.UG.IsUnifV E w ϖ → ∀ (j : ℕ) (c : ℂ), IsClosed {v : V |
      GlobalTheory.LFun.heckeVec (locOn h.summand w) (GlobalTheory.LFun.KGL w n) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) v = c • v} :=
    fun ϖ hϖ j c => isClosed_eq (continuous_heckeVec hρ (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j))
      (continuous_const_smul c)
  change GlobalTheory.LFun.HasSatGL w (π.locRep w) B ↔ _
  constructor
  · intro hB
    refine ⟨?_, fun v hv h0 => ?_⟩
    · obtain ⟨x, hx⟩ := hB.exists_vec
      have h1 := hx.map J hJ fun e => hx.1 (hi (by rw [e, map_zero]))
      exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
    · refine ⟨h0, hv, hB.card, fun ϖ hϖ j hj => ?_⟩
      have hv' := hdense v fun u hu => GlobalTheory.LGrp.mem_fixed.1 hv u hu
      refine closure_minimal ?_ (hcl ϖ hϖ j _) hv'
      rintro _ ⟨x, hx, rfl⟩
      by_cases hx0 : x = 0
      · subst hx0
        simp [GlobalTheory.LFun.heckeVec]
      · exact ((hB.2 x (GlobalTheory.LGrp.mem_fixed.2 hx) hx0).map J hJ
          fun e => hx0 (hi (by rw [e, map_zero]))).2.2.2 ϖ hϖ j hj
  · intro hB
    obtain ⟨v, hv⟩ := hB.exists_vec
    have hv' := hdense v fun u hu => GlobalTheory.LGrp.mem_fixed.1 hv.2.1 u hu
    refine ⟨(Submodule.ne_bot_iff _).2 ?_, fun x hx h0 => ?_⟩
    · by_contra hno
      push_neg at hno
      have hsub : J '' {x | ∀ u ∈ GlobalTheory.LFun.KGL w n, π.locRep w u x = x} ⊆ {0} := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hno x (GlobalTheory.LGrp.mem_fixed.2 hx), map_zero]
        rfl
      exact hv.1 (closure_minimal hsub isClosed_singleton hv')
    · have hJx : J x ∈ GlobalTheory.PRep.fixed (locOn h.summand w) (GlobalTheory.LFun.KGL w n) :=
        GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hJ, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
      exact GlobalTheory.LFun.IsSatVecGL.of_map J hJ hi (hB.2 _ hJx fun e => h0 (hi (by rw [e, map_zero])))
