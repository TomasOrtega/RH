import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RDualC
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SatOfPol

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G V} {ρ : Representation ℂ G W} {K : Subgroup G} {h : G → ℂ} {x : V} {y : W}

/- English proof (translation)
Establish `hf` using `GlobalTheory.LGrp.mem_fixed.1 hx`. Establish `hg` using `GlobalTheory.LGrp.mem_fixed.1 hy`. Establish `bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y` using `fun a ha b hb t => by`. Take `⟨a, rfl⟩` from `θ.surjective a`. Rewrite using `[map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]`.

Conclude with `(congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)`. Establish `bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y)` using `fun a ha b hb t => by`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]`. Conclude with `(congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)`. Establish `inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y)` using `fun t => by`.

Rewrite using `[← hi t⁻¹ x (ρ t y)]`. Simplify using the standard rewrite rules. Establish `e1` using `(β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)`. Establish `e2` using `(β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)`. Use `e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)`. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Distinguish the cases in `h0 : h c.out = 0`. Simplify using `[h0]`. Take `⟨a, ha, b, hb, t, htt, e⟩` from `ht _ h0`.

Use `congr 1`. Rewrite using `[e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]`.
-/
private theorem pair_heckeVec (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed σ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G ≃* G) (hθ : ∀ k, k ∈ K ↔ θ k ∈ K)
    (hi : ∀ g v w, β (σ (θ g) v) (ρ g w) = β v w)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t⁻¹ = t ∧ g = a * t * b) :
    β (heckeVec σ K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y := fun a ha b hb t => by
    obtain ⟨a, rfl⟩ := θ.surjective a
    rw [map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)
  have inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y) := fun t => by
    rw [← hi t⁻¹ x (ρ t y)]; simp
  have e1 := (β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Establish `hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex`. Establish `ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K)` using `(hρ y).preimage continuous_subtype_val`. Use `haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.

Use `⟨GlobalTheory.OrbitAvg.avg ρ K y, GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩` and prove the remaining obligations. Use `haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)`. Establish `hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0` using `by exact_mod_cast hfi.index_ne_zero`. Establish `h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y` using `fun q => hl _ q.out.2 y`. Simplify using `only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]`.

Rewrite using `[Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]`.
-/
private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : W →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : W) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y
  simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in

/- English proof (translation)
Establish `hKc : IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E)))` using `GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)`. Set `c` to `RingEquiv.refl (w.adicCompletion E)`. Establish `hc : ∀ a, Valued.v (c a) = Valued.v a` using `fun _ => rfl`. Establish `hK` using `mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)`. Establish `hfY` using `GlobalTheory.LGrp.mem_fixed.1 hY.2.1`.

Take `⟨x, hxK, hx⟩` from `exists_fixed_pair hσ hKc (β.flip Y) (fun k hk v => by`. Take `⟨k', rfl⟩` from `(GlobalTheory.LFun.ConjPlace.invT c n).surjective k`. Use `hi k' v Y` as an intermediate fact. Rewrite using `[hfY _ ((hK k').2 hk)] at this) x₀` and apply the resulting hypothesis. Establish `hne : β x Y ≠ 0` using `fun h0 => hx₀ (hx.symm.trans h0)`.

Take `⟨p, hp⟩` from `exists_isUnifV w`. Take `⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p` from `⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩`. Take `⟨hcard, hE'⟩` from `hE x hxK`. Use `eq_of_satEig_eq (qV_ne_zero w) hcard hY.2.2.1 fun j hj => ?_` and prove the remaining obligations. Establish `key` using `pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hxK hY.2.1 β (GlobalTheory.LFun.ConjPlace.invT c n) hK hi (fun g hg => by`.

Rewrite `hg` using `[Tj_apply]`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w), g = a * dGL n ϖ j * b := by`. Assume the negation of the conclusion as `hn`. Conclude with `hg (if_neg hn)`. Conclude with `⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)`.

Rewrite `key` using `[hE' _ hp j hj, hY.2.2.2 _ hp j hj, map_smul, smul_eq_mul]`. Conclude with `mul_right_cancel₀ hne key`.
-/
private theorem sat_eq_of_eig {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hσ : IsSmooth σ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n g) x) (ρ g y) = β x y)
    {Y : W} {C C' : Multiset ℂˣ} (hY : IsSatVecGL w ρ Y C') {x₀ : V} (hx₀ : β x₀ Y ≠ 0)
    (hE : ∀ x ∈ fixed σ (KGL w n), C.card = n ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n,
      β (heckeVec σ (KGL w n) (Tj ℂ n (Ov E w) ϖ j) x) Y = satEig (qV E w) n C j * β x Y) : C = C' := by
  classical
  have hKc : IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  have hfY := GlobalTheory.LGrp.mem_fixed.1 hY.2.1
  obtain ⟨x, hxK, hx⟩ := exists_fixed_pair hσ hKc (β.flip Y) (fun k hk v => by
    obtain ⟨k', rfl⟩ := (GlobalTheory.LFun.ConjPlace.invT c n).surjective k
    have := hi k' v Y
    rwa [hfY _ ((hK k').2 hk)] at this) x₀
  have hne : β x Y ≠ 0 := fun h0 => hx₀ (hx.symm.trans h0)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  obtain ⟨hcard, hE'⟩ := hE x hxK
  refine eq_of_satEig_eq (qV_ne_zero w) hcard hY.2.2.1 fun j hj => ?_
  have key := pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hxK hY.2.1 β
    (GlobalTheory.LFun.ConjPlace.invT c n) hK hi
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)
  rw [hE' _ hp j hj, hY.2.2.2 _ hp j hj, map_smul, smul_eq_mul] at key
  exact mul_right_cancel₀ hne key

/- English proof (translation)
Introduce `E _ _ _ V Q B hB hne w T hsm heq hker C C' hC hQ`. Set `σ : Representation ℂ (GL (Fin 2) (Kv w)) V` to `(GlobalTheory.PRep.sub (finRep E 2) V fun k => hB.st (.fin k)).comp (locGL E 2 w)`. Establish `hsmooth : GlobalTheory.PRep.IsSmooth σ`. Introduce `x`. Set `S : Subgroup (GL (Fin 2) (Kv w))` to `{ carrier := {g | σ g x = x} mul_mem' := fun {a b} ha hb => by`.

Express the relevant statement in the definitionally equal form `σ (a * b) x = x`. Rewrite using `[map_mul, Module.End.mul_apply, show σ b x = x from hb]`. Conclude with `ha`. Use the proof step `one_mem' := by change σ 1 x = x; rw [map_one]; rfl`. Use the proof step `inv_mem' := fun {a} ha => by`.

Express the relevant statement in the definitionally equal form `σ a⁻¹ x = x`. Use `conv_lhs => rw [← show σ a x = x from ha]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]`. Use `rfl }`. Use `Subgroup.isOpen_of_mem_nhds S (g := 1) ?_` and prove the remaining obligations.

Use `filter_upwards [hsm x] with y hy`. Conclude with `Subtype.ext (Subtype.ext (funext fun g => hy g))`. Establish `hker0 : ∀ y : Q.V, (∀ x, B x y = 0) → y = 0`. Establish `hst : IsStable ((LinearMap.ker B.flip).map Q.V.subtype)`. Introduce and unpack `o _ ⟨y, hy, rfl⟩`.

Establish `hy' : ∀ x, B x y = 0` using `fun x => LinearMap.congr_fun (LinearMap.mem_ker.1 hy) x`. Use `⟨Q.op o y, LinearMap.mem_ker.2 (LinearMap.ext fun x => ?_), rfl⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `B x (Q.op o y) = 0`. Consider the cases of `o with`. Consider the case `fin k`.

Set `x' : V` to `⟨act (.fin k⁻¹) x.1, hB.st _ _ x.2⟩`. Establish `e : (⟨act (.fin k) x'.1, hB.st _ _ x'.2⟩ : V) = x` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `finRep E 2 k (finRep E 2 k⁻¹ x.1) = x.1`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Use the proof step `rfl)`.

Conclude with `(congrArg (fun u => B u (Q.op (.fin k) y)) e).symm.trans ((hB.fin k x' y).trans (hy' x'))`. Consider the case `cpt k`. Set `x' : V` to `⟨act (.cpt k⁻¹) x.1, hB.st _ _ x.2⟩`. Establish `e : (⟨act (.cpt k) x'.1, hB.st _ _ x'.2⟩ : V) = x` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `cptRep E 2 k (cptRep E 2 k⁻¹ x.1) = x.1`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]`. Use the proof step `rfl)`. Conclude with `(congrArg (fun u => B u (Q.op (.cpt k) y)) e).symm.trans ((hB.cpt k x' y).trans (hy' x'))`. Consider the case `lie X`. Establish `h` using `hB.lie X x y`.

Rewrite `h` using `[hy' _, zero_add]`. Conclude with `h`. Introduce `y hy`. Break down `Q.irred _ (Submodule.map_subtype_le _ _) hst with h | h` into its components or cases. Establish `hm : y.1 ∈ (LinearMap.ker B.flip).map Q.V.subtype` using `⟨y, LinearMap.mem_ker.2 (LinearMap.ext hy), rfl⟩`.

Rewrite `hm` using `[h]`. Conclude with `Subtype.ext ((Submodule.mem_bot _).1 hm)`. It suffices to derive a contradiction. Use `hne (LinearMap.ext fun x => LinearMap.ext fun z => ?_)` and prove the remaining obligations. Establish `hz : z.1 ∈ (LinearMap.ker B.flip).map Q.V.subtype` using `by rw [h]; exact z.2`.

Take `⟨u, hu, e⟩` from `hz`. Establish `e' : u = z` using `Subtype.ext e`. Substitute `e'` using the available equality. Conclude with `LinearMap.congr_fun (LinearMap.mem_ker.1 hu) x`. Establish `hD` using `TC.hasSatGL_dual ((CG.hasSat_mk Q w C').1 hQ)`.

Take `⟨Y, hY⟩` from `hD.exists_vec`. Set `β : V →ₗ[ℂ] (TC.dual Q).V →ₗ[ℂ] ℂ` to `B.compl₂ (TC.toDual Q).symm.toLinearMap`. Establish `hβ : ∀ x y, β x (TC.toDual Q y) = B x y` using `fun x y => by simp [β]`. Establish `hβ' : ∀ x, β x Y = B x ((TC.toDual Q).symm Y)` using `fun _ => rfl`. Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x₀, β x₀ Y ≠ 0 := by`.

Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Use `hY.1 ?_` and prove the remaining obligations. Establish `h0` using `hker0 ((TC.toDual Q).symm Y) hn`. Simplify using `using h0`.

Establish `hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) 2 g) x) ((TC.dual Q).locRep w g y) = β x y`. Introduce `g x y`. Take `⟨y, rfl⟩` from `(TC.toDual Q).surjective y`. Rewrite using `[TC.locRep_toDual, hβ, hβ]`. Establish `e` using `hB.fin (locGL E 2 w (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) 2 g)) x y`.

Use `Eq.trans ?_ e` and prove the remaining obligations. Use `congrArg (B _) ?_` and prove the remaining obligations. Rewrite using `[CuspSub.locRep_eq]`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `act (.fin _) y.1 = act (.fin _) y.1`.

Use `congrArg (fun k => act (.fin (locGL E 2 w k)) y.1) (Units.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations. Rewrite using `[GlobalTheory.LFun.ConjPlace.invT_val]`. Both sides reduce to the same expression. Establish `hfin` using `sat_eq_of_eig (n := 2) hsmooth β hi hY hx₀ (fun x hx => by`. Establish `hfix : Fix w x.1.1` using `fun g k hk => congrArg (fun u : V => u.1.1 g) (GlobalTheory.LGrp.mem_fixed.1 hx k hk)`.

Use `⟨(hC x hfix 1).card, fun ϖ hϖ j hj => ?_⟩` and prove the remaining obligations. Establish `hTz : ∀ g, T (GlobalTheory.LFun.heckeVec σ (GlobalTheory.LFun.KGL w 2) (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j) x) g = GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 C j * T x g`. Introduce `g`. Set `L : V →+ ℂ` to `(Pi.evalAddMonoidHom _ g).comp T.toAddMonoidHom`. Establish `e1` using `L.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) σ x)`.

Establish `e2` using `(hC x hfix g).eig ϖ hϖ j hj 1`. Use `e1.trans (Eq.trans (finsum_congr fun c => ?_) (e2.trans ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `T (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out • σ c.out x) g = _`. Rewrite using `[map_smul, Pi.smul_apply, smul_eq_mul, heq x (σ c.out x) c.out (fun _ => rfl) g, one_mul]`. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Establish `hz : T (GlobalTheory.LFun.heckeVec σ (GlobalTheory.LFun.KGL w 2) (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j) x - GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 C j • x) = 0`. Use function extensionality and compare the values at `g`. Simplify using `[map_sub, hTz]`. Establish `h2` using `LinearMap.congr_fun (hker _ hz) ((TC.toDual Q).symm Y)`.

Rewrite `h2` using `[map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply, sub_eq_zero, smul_eq_mul]`. Conclude with `h2)`. Rewrite using `[hfin, Multiset.map_map]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.satPair :
    SatPair := by
  intro E _ _ _ V Q B hB hne w T hsm heq hker C C' hC hQ
  classical
  let σ : Representation ℂ (GL (Fin 2) (Kv w)) V :=
    (GlobalTheory.PRep.sub (finRep E 2) V fun k => hB.st (.fin k)).comp (locGL E 2 w)
  have hsmooth : GlobalTheory.PRep.IsSmooth σ := by
    intro x
    let S : Subgroup (GL (Fin 2) (Kv w)) :=
      { carrier := {g | σ g x = x}
        mul_mem' := fun {a b} ha hb => by
          change σ (a * b) x = x
          rw [map_mul, Module.End.mul_apply, show σ b x = x from hb]; exact ha
        one_mem' := by change σ 1 x = x; rw [map_one]; rfl
        inv_mem' := fun {a} ha => by
          change σ a⁻¹ x = x
          conv_lhs => rw [← show σ a x = x from ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    refine Subgroup.isOpen_of_mem_nhds S (g := 1) ?_
    filter_upwards [hsm x] with y hy
    exact Subtype.ext (Subtype.ext (funext fun g => hy g))
  have hker0 : ∀ y : Q.V, (∀ x, B x y = 0) → y = 0 := by
    have hst : IsStable ((LinearMap.ker B.flip).map Q.V.subtype) := by
      rintro o _ ⟨y, hy, rfl⟩
      have hy' : ∀ x, B x y = 0 := fun x => LinearMap.congr_fun (LinearMap.mem_ker.1 hy) x
      refine ⟨Q.op o y, LinearMap.mem_ker.2 (LinearMap.ext fun x => ?_), rfl⟩
      change B x (Q.op o y) = 0
      cases o with
      | fin k =>
        let x' : V := ⟨act (.fin k⁻¹) x.1, hB.st _ _ x.2⟩
        have e : (⟨act (.fin k) x'.1, hB.st _ _ x'.2⟩ : V) = x := Subtype.ext (by
          change finRep E 2 k (finRep E 2 k⁻¹ x.1) = x.1
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
        exact (congrArg (fun u => B u (Q.op (.fin k) y)) e).symm.trans ((hB.fin k x' y).trans (hy' x'))
      | cpt k =>
        let x' : V := ⟨act (.cpt k⁻¹) x.1, hB.st _ _ x.2⟩
        have e : (⟨act (.cpt k) x'.1, hB.st _ _ x'.2⟩ : V) = x := Subtype.ext (by
          change cptRep E 2 k (cptRep E 2 k⁻¹ x.1) = x.1
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl)
        exact (congrArg (fun u => B u (Q.op (.cpt k) y)) e).symm.trans ((hB.cpt k x' y).trans (hy' x'))
      | lie X =>
        have h := hB.lie X x y
        rw [hy' _, zero_add] at h
        exact h
    intro y hy
    rcases Q.irred _ (Submodule.map_subtype_le _ _) hst with h | h
    · have hm : y.1 ∈ (LinearMap.ker B.flip).map Q.V.subtype :=
        ⟨y, LinearMap.mem_ker.2 (LinearMap.ext hy), rfl⟩
      rw [h] at hm
      exact Subtype.ext ((Submodule.mem_bot _).1 hm)
    · exfalso
      refine hne (LinearMap.ext fun x => LinearMap.ext fun z => ?_)
      have hz : z.1 ∈ (LinearMap.ker B.flip).map Q.V.subtype := by rw [h]; exact z.2
      obtain ⟨u, hu, e⟩ := hz
      have e' : u = z := Subtype.ext e
      subst e'
      exact LinearMap.congr_fun (LinearMap.mem_ker.1 hu) x
  have hD := TC.hasSatGL_dual ((CG.hasSat_mk Q w C').1 hQ)
  obtain ⟨Y, hY⟩ := hD.exists_vec
  let β : V →ₗ[ℂ] (TC.dual Q).V →ₗ[ℂ] ℂ := B.compl₂ (TC.toDual Q).symm.toLinearMap
  have hβ : ∀ x y, β x (TC.toDual Q y) = B x y := fun x y => by simp [β]
  have hβ' : ∀ x, β x Y = B x ((TC.toDual Q).symm Y) := fun _ => rfl
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, β x₀ Y ≠ 0 := by
    by_contra hn
    push_neg at hn
    refine hY.1 ?_
    have h0 := hker0 ((TC.toDual Q).symm Y) hn
    simpa using h0
  have hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) 2 g) x) ((TC.dual Q).locRep w g y) = β x y := by
    intro g x y
    obtain ⟨y, rfl⟩ := (TC.toDual Q).surjective y
    rw [TC.locRep_toDual, hβ, hβ]
    have e := hB.fin (locGL E 2 w (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) 2 g)) x y
    refine Eq.trans ?_ e
    refine congrArg (B _) ?_
    rw [CuspSub.locRep_eq]
    refine Subtype.ext ?_
    change act (.fin _) y.1 = act (.fin _) y.1
    refine congrArg (fun k => act (.fin (locGL E 2 w k)) y.1) (Units.ext (Matrix.ext fun i j => ?_))
    rw [GlobalTheory.LFun.ConjPlace.invT_val]
    rfl
  have hfin := sat_eq_of_eig (n := 2) hsmooth β hi hY hx₀ (fun x hx => by
    have hfix : Fix w x.1.1 := fun g k hk => congrArg (fun u : V => u.1.1 g) (GlobalTheory.LGrp.mem_fixed.1 hx k hk)
    refine ⟨(hC x hfix 1).card, fun ϖ hϖ j hj => ?_⟩
    have hTz : ∀ g, T (GlobalTheory.LFun.heckeVec σ (GlobalTheory.LFun.KGL w 2) (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j) x) g =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 C j * T x g := by
      intro g
      let L : V →+ ℂ := (Pi.evalAddMonoidHom _ g).comp T.toAddMonoidHom
      have e1 := L.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w 2) (GlobalTheory.LFun.Tj_mem_hecke hϖ j) σ x)
      have e2 := (hC x hfix g).eig ϖ hϖ j hj 1
      refine e1.trans (Eq.trans (finsum_congr fun c => ?_) (e2.trans ?_))
      · change T (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j c.out • σ c.out x) g = _
        rw [map_smul, Pi.smul_apply, smul_eq_mul, heq x (σ c.out x) c.out (fun _ => rfl) g, one_mul]
        rfl
      · simp
    have hz : T (GlobalTheory.LFun.heckeVec σ (GlobalTheory.LFun.KGL w 2) (Formalism.UG.Tj ℂ 2 (Formalism.UG.Ov E w) ϖ j) x -
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) 2 C j • x) = 0 := by
      funext g
      simp [map_sub, hTz]
    have h2 := LinearMap.congr_fun (hker _ hz) ((TC.toDual Q).symm Y)
    rw [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.zero_apply, sub_eq_zero, smul_eq_mul] at h2
    exact h2)
  rw [hfin, Multiset.map_map]
  simp
