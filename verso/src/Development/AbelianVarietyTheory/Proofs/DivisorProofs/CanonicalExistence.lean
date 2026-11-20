import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

/- English proof (translation)
Take `⟨g, hg⟩` from `(Fintype.linearCombination (FractionRing O) m).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hm.fintypeLinearCombination_injective)`. Establish `hgm : ∀ a, g (m a) = Pi.single a 1` using `fun a => by`. Establish `h` using `LinearMap.congr_fun hg (Pi.single a 1)`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, Fintype.linearCombination_apply_single, one_smul] at h`. Conclude with `h`.

Set `κ : FractionRing O →ₐ[O] K'` to `IsFractionRing.liftAlgHom (K := FractionRing O) (g := Algebra.ofId O K') hO`. Set `φ : M →ₗ[O] (Fin n → K')` to `LinearMap.pi fun k => κ.toLinearMap.comp ((LinearMap.proj k).comp (g.restrictScalars O))`. Set `F` to `φ.liftBaseChange K'`. Establish `hF : ∀ a, F ((1 : K') ⊗ₜ[O] m a) = Pi.single a 1` using `fun a => by`. Simplify using `only [F, LinearMap.liftBaseChange_tmul, one_smul]`.

Use function extensionality and compare the values at `k`. Simplify using `only [φ, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.proj_apply, hgm, AlgHom.toLinearMap_apply]`. Distinguish the cases in `h : k = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Pi.single_apply, h]`. Use `LinearIndependent.of_comp F ?_` and prove the remaining obligations. Establish `: (F ∘ fun a => ((1 : K') ⊗ₜ[O] m a : K' ⊗[O] M)) = fun a => Pi.single a (1 : K')` using `funext hF`. Rewrite using `[this]`. Use `(Pi.basisFun K' (Fin n)).linearIndependent using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `a`. Simplify using the standard rewrite rules.
-/
theorem li_one_tmul_of_li {O K' M : Type} [CommRing O] [IsDomain O] [Field K'] [Algebra O K']
    (hO : Function.Injective (algebraMap O K'))
    [AddCommGroup M] [Module (FractionRing O) M] [Module O M] [IsScalarTower O (FractionRing O) M] {n : ℕ} (m : Fin n → M)
    (hm : LinearIndependent (FractionRing O) m) :
    LinearIndependent K' fun a => ((1 : K') ⊗ₜ[O] m a : K' ⊗[O] M) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination (FractionRing O) m).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hm.fintypeLinearCombination_injective)
  have hgm : ∀ a, g (m a) = Pi.single a 1 := fun a => by
    have h := LinearMap.congr_fun hg (Pi.single a 1)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Fintype.linearCombination_apply_single, one_smul] at h
    exact h
  let κ : FractionRing O →ₐ[O] K' := IsFractionRing.liftAlgHom (K := FractionRing O) (g := Algebra.ofId O K') hO
  let φ : M →ₗ[O] (Fin n → K') := LinearMap.pi fun k =>
    κ.toLinearMap.comp ((LinearMap.proj k).comp (g.restrictScalars O))
  let F := φ.liftBaseChange K'
  have hF : ∀ a, F ((1 : K') ⊗ₜ[O] m a) = Pi.single a 1 := fun a => by
    simp only [F, LinearMap.liftBaseChange_tmul, one_smul]
    funext k
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.proj_apply, hgm,
      AlgHom.toLinearMap_apply]
    by_cases h : k = a
    · subst h; simp
    · simp [Pi.single_apply, h]
  refine LinearIndependent.of_comp F ?_
  have : (F ∘ fun a => ((1 : K') ⊗ₜ[O] m a : K' ⊗[O] M)) = fun a => Pi.single a (1 : K') := funext hF
  rw [this]
  convert (Pi.basisFun K' (Fin n)).linearIndependent using 1
  funext a
  simp

/- English proof (translation)
Use `set e0 := (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) (S.kKs a) with he0`. Take `⟨y, z, hz, hyz⟩` from `IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) e0`. Establish `hz0 : z ≠ 0` using `nonZeroDivisors.ne_zero hz`. Establish `hz' : algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz`. Establish `hE : e0 * algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z = algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) y`.

Rewrite using `[← hyz, div_mul_cancel₀ _ hz']`. Establish `h1` using `hc.embedding_baseField_condition w (S.kKs a) y z hz0 hE`. Rewrite `h1` using `[S.kKs_spec]`. Use `set zO := algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z with hzO`. Use `set yO := algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y with hyO`.

Establish `hφ : ∀ u : D.ntw.O (c.twI w), algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) u = algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w) (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) u))` using `fun u => by`. Rewrite using `[IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (c.Oe w) (FractionRing (c.Oe w)), IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]`. Establish `hι : (show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) * algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) zO = algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) yO`. Establish `hm : ∀ u : D.ntw.O0 (c.twI w), IsFractionRing.map (A` using `D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O0 (c.twI w))) (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w)) (algebraMap _ _ u) = algebraMap (D.ntw.O (c.twI w)) _ (algebraMap _ _ u) := fun u => IsLocalization.map_eq _ _`. Express the relevant statement in the definitionally equal form `(IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O0 (c.twI w))) (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) e0 * _ = _`.

Rewrite using `[hzO, hyO, ← hm, ← hm, ← map_mul, hE]`. Establish `hζ : algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) zO ≠ 0`. Rewrite using `[hφ]`. Introduce `h0`. Apply `hz0` to reduce the goal to its premises.

Use `IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (h0.trans (map_zero _).symm)` as an intermediate fact. Use `c.Oe_inj w (this.trans (map_zero _).symm)` as an intermediate fact. Use `D.ntw.Ok_inj (c.twI w) (c.k' w) (this.trans (map_zero _).symm)` as an intermediate fact. Conclude with `D.ntw.O_inj (c.twI w) (this.trans (map_zero _).symm)`. Establish `key : ∀ t : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M, zO • t = algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) zO • t` using `fun t => (algebraMap_smul (FractionRing (c.Oe w)) zO t).symm`.

Establish `hL : zO • (c.embW w (algebraMap S.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (c.twI w)] m : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) = (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] (yO • m)`. Rewrite using `[TensorProduct.smul_tmul', Algebra.smul_def, hφ, mul_comm, h1, ← hφ, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Establish `hR : zO • ((1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] ((show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) • m) : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) = (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] (yO • m)`. Rewrite using `[← TensorProduct.tmul_smul]`. Use `congr 1`.

Rewrite using `[← algebraMap_smul (FractionRing (D.ntw.O (c.twI w))) zO, smul_smul, mul_comm, hι, algebraMap_smul]`. Establish `h2` using `(key _).symm.trans (hL.trans (hR.symm.trans (key _)))`. Conclude with `smul_right_injective _ hζ h2`.
-/
theorem embW_tmul_eq {D : D7} (S : NX.RatDat D.ntw) (c : NChoice D) (hc : NChTie D c) (w : D.what₂.places.Pl) {M : Type}
    [AddCommGroup M] [Module (FractionRing (D.ntw.O (c.twI w))) M] [Module (D.ntw.O (c.twI w)) M]
    [IsScalarTower (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) M] (a : S.Ks) (m : M) :
    (c.embW w (algebraMap S.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (c.twI w)] m : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)]
        ((show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) • m) := by
  classical
  set e0 := (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) (S.kKs a) with he0
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) e0
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz' : algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  have hE : e0 * algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) y := by
    rw [← hyz, div_mul_cancel₀ _ hz']
  have h1 := hc.embedding_baseField_condition w (S.kKs a) y z hz0 hE
  rw [S.kKs_spec] at h1
  set zO := algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z with hzO
  set yO := algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y with hyO
  have hφ : ∀ u : D.ntw.O (c.twI w), algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) u =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) u)) := fun u => by
    rw [IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (c.Oe w) (FractionRing (c.Oe w)),
      IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]
  have hι : (show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) *
      algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) zO = algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) yO := by
    have hm : ∀ u : D.ntw.O0 (c.twI w), IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O0 (c.twI w)))
        (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w)) (algebraMap _ _ u) = algebraMap (D.ntw.O (c.twI w)) _ (algebraMap _ _ u) :=
      fun u => IsLocalization.map_eq _ _
    change (IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O0 (c.twI w)))
        (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) e0 * _ = _
    rw [hzO, hyO, ← hm, ← hm, ← map_mul, hE]
  have hζ : algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) zO ≠ 0 := by
    rw [hφ]
    intro h0
    apply hz0
    have := IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (h0.trans (map_zero _).symm)
    have := c.Oe_inj w (this.trans (map_zero _).symm)
    have := D.ntw.Ok_inj (c.twI w) (c.k' w) (this.trans (map_zero _).symm)
    exact D.ntw.O_inj (c.twI w) (this.trans (map_zero _).symm)
  have key : ∀ t : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M,
      zO • t = algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) zO • t :=
    fun t => (algebraMap_smul (FractionRing (c.Oe w)) zO t).symm
  have hL : zO • (c.embW w (algebraMap S.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (c.twI w)] m : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] (yO • m) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, hφ, mul_comm, h1, ← hφ, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have hR : zO • ((1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)]
      ((show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) • m) : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] (yO • m) := by
    rw [← TensorProduct.tmul_smul]
    congr 1
    rw [← algebraMap_smul (FractionRing (D.ntw.O (c.twI w))) zO, smul_smul, mul_comm, hι, algebraMap_smul]
  have h2 := (key _).symm.trans (hL.trans (hR.symm.trans (key _)))
  exact smul_right_injective _ hζ h2

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

/- English proof (translation)
Take `⟨n, b, hbK, hliK, hspK, hliL, hspL⟩` from `p.fw.ks j`. Establish `hEs : ∀ (a : p.Sx.Ks) (v : p.Sx.WL ((j : ℕ) + 1)), (p.nexp.fi j).e (a • v) = (p.nexp.fi j).eK a • (p.nexp.fi j).e v` using `fun a v => by`. Rewrite using `[← algebraMap_smul D.what₂.LL a v, LinearEquiv.map_smul, ← (p.nexp.fi j).eK_LL, algebraMap_smul]`. Set `f : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)` to `fun k => ⟨(p.nexp.fi j).e.symm (b k), ((p.nexp.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hbK k)⟩`. Establish `hf : ∀ k, (p.nexp.fi j).e (f k).1 = b k` using `fun k => LinearEquiv.apply_symm_apply _ _`.

Set `v : NX.FmK p.Sx ((j : ℕ) + 1) →ₗ[p.Sx.Ks] p.Sx.WL ((j : ℕ) + 1)` to `(p.Sx.A ((j : ℕ) + 1)).WK.subtype`. Establish `hv : ∀ g, v g = g.1` using `fun _ => rfl`. Establish `hsum : ∀ a : Fin n → p.Sx.Ks, (p.nexp.fi j).e (∑ k, a k • f k).1 = ∑ k, (p.nexp.fi j).eK (a k) • b k`. Introduce `a`. Rewrite using `[← hv, map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hv, hEs, hf]`. Establish `hdec : ∀ g : NX.FmK p.Sx ((j : ℕ) + 1), ∃ a : Fin n → p.Sx.Ks, g = ∑ k, a k • f k`. Introduce `g`. Establish `hg : (p.nexp.fi j).e g.1 ∈ (p.R.FW j).WK` using `((p.nexp.fi j).wk _).1 g.2`.

Rewrite `hg` using `[← hspK, Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `hg`. Use `⟨fun k => (p.nexp.fi j).eK.symm (c k), Subtype.ext ((p.nexp.fi j).e.injective ?_)⟩` and prove the remaining obligations. Rewrite using `[hsum, ← hc]`. Simplify using `only [RingEquiv.apply_symm_apply]`.

Establish `hliF : LinearIndependent p.Sx.Ks f`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha k`. Establish `h0 : ∑ k, (p.nexp.fi j).eK (a k) • b k = 0`. Rewrite using `[← hsum, ha, ← hv, map_zero, map_zero]`.

Use `(Fintype.linearIndependent_iff.1 hliK) _ h0 k` as an intermediate fact. Conclude with `(map_eq_zero_iff _ (p.nexp.fi j).eK.injective).1 this`. Set `bK : Module.Basis (Fin n) p.Sx.Ks (NX.FmK p.Sx ((j : ℕ) + 1))` to `Module.Basis.mk hliF (fun g _ => by`. Take `⟨a, rfl⟩` from `hdec g`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))`.

Use `set eF := p.nexp.eF (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) (Nat.le_add_left _ _) j.2 with heF`. Set `m : Fin n → D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w)` to `fun k => eF.symm ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k)`. Set `t : Fin n → Tgt ex w j` to `fun k => (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m k`. Set `β : Module.Basis (Fin n) D.what₂.LL (Fin ((R2 p).nW j) → D.what₂.LL)` to `Module.Basis.mk hliL hspL.ge`. Establish `hβ : ∀ k, β k = b k` using `fun k => Module.Basis.mk_apply _ _ _`.

Set `rd : Can p w j` to `{ toFun := fun x => ∑ k, ex.nch.embW w (β.equivFun x k) • t k map_add' := fun x y => by simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib] map_smul' := fun c x => by`. Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }`. Establish `hrd : ∀ x, rd x = ∑ k, ex.nch.embW w (β.equivFun x k) • t k` using `fun _ => rfl`. Use `⟨rd, fun g => ?_, n, β, ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hdec g`.

Establish `hx : (p.nexp.fi j).e (∑ k, a k • f k).1 = β.equivFun.symm fun k => algebraMap p.Sx.Ks D.what₂.LL (a k)`. Rewrite using `[hsum, Module.Basis.equivFun_symm_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hβ, ← (p.nexp.fi j).eK_LL]`. Conclude with `(algebraMap_smul D.what₂.LL _ _).symm`.

Establish `hterm : ∀ k, ex.nch.embW w (algebraMap p.Sx.Ks D.what₂.LL (a k)) • t k = (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] eF.symm ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] (a k • f k))` using `fun k => by`. Simplify using `only [t, m]`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one, embW_tmul_eq p.Sx ex.nch ex.nch_tie w]`. Use `congr 1`. Rewrite using `[TensorProduct.tmul_smul, ← algebraMap_smul (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) (a k)]`.

Conclude with `(eF.symm.map_smul _ _).symm`. Use `(hrd _).trans ?_` and prove the remaining obligations. Rewrite using `[hx, LinearEquiv.apply_symm_apply, Finset.sum_congr rfl fun k _ => hterm k, ← TensorProduct.tmul_sum]`. Use `congr 1`. Rewrite using `[TensorProduct.tmul_sum]`.

Conclude with `(map_sum eF.symm _ _).symm`. Establish `hB : LinearIndependent (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) fun k => ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w) ⊗[p.Sx.Ks] NX.FmK p.Sx ((j : ℕ) + 1))`. Use `(Algebra.TensorProduct.basis (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) bK).linearIndependent` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`.

Rewrite using `[Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]`. Set `u : Fin n → NX.Fm p.Sx (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w)` to `fun k => (1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k`. Establish `hB' : LinearIndependent (FractionRing (D.ntw.O (ex.nch.twI w))) u` using `hB`. Establish `hm : LinearIndependent (FractionRing (D.ntw.O (ex.nch.twI w))) m` using `hB'.map' eF.symm.toLinearMap eF.symm.ker`. Establish `hO : Function.Injective (algebraMap (D.ntw.O (ex.nch.twI w)) (FractionRing (ex.nch.Oe w)))`.

Establish `e1 : algebraMap (D.ntw.O (ex.nch.twI w)) (FractionRing (ex.nch.Oe w)) = (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))).comp ((algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w)).comp (algebraMap (D.ntw.O (ex.nch.twI w)) (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w …`. Rewrite using `[← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]`. Rewrite using `[e1, RingHom.coe_comp, RingHom.coe_comp]`. Conclude with `(IsFractionRing.injective _ _).comp ((ex.nch.Oe_inj w).comp (D.ntw.Ok_inj _ _))`. Establish `hrb : ∀ a, rd (β a) = t a` using `fun a => by`.

Rewrite using `[hrd, Finset.sum_eq_single a]`. Simplify using `[Module.Basis.equivFun_self]`. Introduce `k _ hk`. Simplify using `[Module.Basis.equivFun_self, Ne.symm hk]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ a) h`. Use `li_one_tmul_of_li (K' := FractionRing (ex.nch.Oe w)) hO m hm` as an intermediate fact. Establish `ht : (fun a => rd (β a)) = t` using `funext hrb`. Rewrite using `[ht]`. Conclude with `this`.
-/
theorem canEx_at (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m) :
    ∃ rd : Can p w j, IsCan p rd ∧ ∃ (n : ℕ) (β : Module.Basis (Fin n) D.what₂.LL (Fin ((R2 p).nW j) → D.what₂.LL)),
      LinearIndependent (FractionRing (ex.nch.Oe w)) fun a => rd (β a) := by
  classical
  obtain ⟨n, b, hbK, hliK, hspK, hliL, hspL⟩ := p.fw.ks j
  have hEs : ∀ (a : p.Sx.Ks) (v : p.Sx.WL ((j : ℕ) + 1)), (p.nexp.fi j).e (a • v) = (p.nexp.fi j).eK a • (p.nexp.fi j).e v :=
    fun a v => by
      rw [← algebraMap_smul D.what₂.LL a v, LinearEquiv.map_smul, ← (p.nexp.fi j).eK_LL, algebraMap_smul]
  let f : Fin n → NX.FmK p.Sx ((j : ℕ) + 1) := fun k =>
    ⟨(p.nexp.fi j).e.symm (b k), ((p.nexp.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hbK k)⟩
  have hf : ∀ k, (p.nexp.fi j).e (f k).1 = b k := fun k => LinearEquiv.apply_symm_apply _ _
  let v : NX.FmK p.Sx ((j : ℕ) + 1) →ₗ[p.Sx.Ks] p.Sx.WL ((j : ℕ) + 1) := (p.Sx.A ((j : ℕ) + 1)).WK.subtype
  have hv : ∀ g, v g = g.1 := fun _ => rfl
  have hsum : ∀ a : Fin n → p.Sx.Ks, (p.nexp.fi j).e (∑ k, a k • f k).1 = ∑ k, (p.nexp.fi j).eK (a k) • b k := by
    intro a
    rw [← hv, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hv, hEs, hf]
  have hdec : ∀ g : NX.FmK p.Sx ((j : ℕ) + 1), ∃ a : Fin n → p.Sx.Ks, g = ∑ k, a k • f k := by
    intro g
    have hg : (p.nexp.fi j).e g.1 ∈ (p.R.FW j).WK := ((p.nexp.fi j).wk _).1 g.2
    rw [← hspK, Submodule.mem_span_range_iff_exists_fun] at hg
    obtain ⟨c, hc⟩ := hg
    refine ⟨fun k => (p.nexp.fi j).eK.symm (c k), Subtype.ext ((p.nexp.fi j).e.injective ?_)⟩
    rw [hsum, ← hc]
    simp only [RingEquiv.apply_symm_apply]
  have hliF : LinearIndependent p.Sx.Ks f := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have h0 : ∑ k, (p.nexp.fi j).eK (a k) • b k = 0 := by
      rw [← hsum, ha, ← hv, map_zero, map_zero]
    have := (Fintype.linearIndependent_iff.1 hliK) _ h0 k
    exact (map_eq_zero_iff _ (p.nexp.fi j).eK.injective).1 this
  let bK : Module.Basis (Fin n) p.Sx.Ks (NX.FmK p.Sx ((j : ℕ) + 1)) := Module.Basis.mk hliF (fun g _ => by
    obtain ⟨a, rfl⟩ := hdec g
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  set eF := p.nexp.eF (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) (Nat.le_add_left _ _) j.2 with heF
  let m : Fin n → D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) := fun k =>
    eF.symm ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k)
  let t : Fin n → Tgt ex w j := fun k => (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m k
  let β : Module.Basis (Fin n) D.what₂.LL (Fin ((R2 p).nW j) → D.what₂.LL) := Module.Basis.mk hliL hspL.ge
  have hβ : ∀ k, β k = b k := fun k => Module.Basis.mk_apply _ _ _
  let rd : Can p w j :=
    { toFun := fun x => ∑ k, ex.nch.embW w (β.equivFun x k) • t k
      map_add' := fun x y => by simp only [map_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }
  have hrd : ∀ x, rd x = ∑ k, ex.nch.embW w (β.equivFun x k) • t k := fun _ => rfl
  refine ⟨rd, fun g => ?_, n, β, ?_⟩
  · obtain ⟨a, rfl⟩ := hdec g
    have hx : (p.nexp.fi j).e (∑ k, a k • f k).1 = β.equivFun.symm fun k => algebraMap p.Sx.Ks D.what₂.LL (a k) := by
      rw [hsum, Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hβ, ← (p.nexp.fi j).eK_LL]
      exact (algebraMap_smul D.what₂.LL _ _).symm
    have hterm : ∀ k, ex.nch.embW w (algebraMap p.Sx.Ks D.what₂.LL (a k)) • t k =
        (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          eF.symm ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] (a k • f k)) := fun k => by
      simp only [t, m]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, embW_tmul_eq p.Sx ex.nch ex.nch_tie w]
      congr 1
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) (a k)]
      exact (eF.symm.map_smul _ _).symm
    refine (hrd _).trans ?_
    rw [hx, LinearEquiv.apply_symm_apply, Finset.sum_congr rfl fun k _ => hterm k, ← TensorProduct.tmul_sum]
    congr 1
    rw [TensorProduct.tmul_sum]
    exact (map_sum eF.symm _ _).symm
  · have hB : LinearIndependent (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) fun k =>
        ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k :
          NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w) ⊗[p.Sx.Ks] NX.FmK p.Sx ((j : ℕ) + 1)) := by
      have := (Algebra.TensorProduct.basis (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) bK).linearIndependent
      convert this using 1
      funext k
      rw [Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
    let u : Fin n → NX.Fm p.Sx (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) := fun k =>
      (1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k
    have hB' : LinearIndependent (FractionRing (D.ntw.O (ex.nch.twI w))) u := hB
    have hm : LinearIndependent (FractionRing (D.ntw.O (ex.nch.twI w))) m := hB'.map' eF.symm.toLinearMap eF.symm.ker
    have hO : Function.Injective (algebraMap (D.ntw.O (ex.nch.twI w)) (FractionRing (ex.nch.Oe w))) := by
      have e1 : algebraMap (D.ntw.O (ex.nch.twI w)) (FractionRing (ex.nch.Oe w)) =
          (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))).comp
            ((algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w)).comp
              (algebraMap (D.ntw.O (ex.nch.twI w)) (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)))) := by
        rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
      rw [e1, RingHom.coe_comp, RingHom.coe_comp]
      exact (IsFractionRing.injective _ _).comp ((ex.nch.Oe_inj w).comp (D.ntw.Ok_inj _ _))
    have hrb : ∀ a, rd (β a) = t a := fun a => by
      rw [hrd, Finset.sum_eq_single a]
      · simp [Module.Basis.equivFun_self]
      · intro k _ hk
        simp [Module.Basis.equivFun_self, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ a) h
    have := li_one_tmul_of_li (K' := FractionRing (ex.nch.Oe w)) hO m hm
    have ht : (fun a => rd (β a)) = t := funext hrb
    rw [ht]
    exact this

end Point

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p _ _ w _ j => canEx_at p w j⟩⟩⟩`.
-/
theorem canEx_holds : CanEx :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ => ⟨0, fun _ _ _ _ p _ _ w _ j => canEx_at p w j⟩⟩⟩

end GlobalTheory.BigOn.Exp
