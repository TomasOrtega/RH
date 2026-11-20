import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffMonicPolySum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.TypeTieProof

/- English proof (translation)
Set `bC : Module.Basis ι ℂ W` to `Module.Basis.mk hli hsp.ge`. Use `⟨bC.constr ℂ (fun k => f (b k)), fun v => ?_⟩` and prove the remaining obligations. Establish `h : (bC.constr ℂ (fun k => f (b k))).comp j = f`. Use `b.ext fun k => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply]`.

Establish `: j (b k) = bC k` using `by simp [bC]`. Rewrite using `[this, Module.Basis.constr_basis]`. Conclude with `congrArg (fun g : V →ₛₗ[σ] U => g v) h`.
-/
theorem exists_ext_semilin {L V W U ι : Type} [Field L] [AddCommGroup V] [Module L V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] (σ : L →+* ℂ) (j : V →ₛₗ[σ] W) (b : Module.Basis ι L V)
    (hli : LinearIndependent ℂ (fun k => j (b k))) (hsp : Submodule.span ℂ (Set.range (fun k => j (b k))) = ⊤)
    (f : V →ₛₗ[σ] U) : ∃ F : W →ₗ[ℂ] U, ∀ v, F (j v) = f v := by
  let bC : Module.Basis ι ℂ W := Module.Basis.mk hli hsp.ge
  refine ⟨bC.constr ℂ (fun k => f (b k)), fun v => ?_⟩
  have h : (bC.constr ℂ (fun k => f (b k))).comp j = f := by
    refine b.ext fun k => ?_
    rw [LinearMap.comp_apply]
    have : j (b k) = bC k := by simp [bC]
    rw [this, Module.Basis.constr_basis]
  exact congrArg (fun g : V →ₛₗ[σ] U => g v) h

/- English proof (translation)
Take `⟨f, hf, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp H v).1 (by rw [htop]; exact Submodule.mem_top)`. Establish `h0 : ∀ x0, x0 ∉ Y → f x0 = 0`. Introduce `x0 hx0`. Distinguish the cases in `hs : x0 ∈ f.support`. Establish `e : f x0 = v - ∑ x ∈ f.support.erase x0, f x`.

Rewrite using `[← hsum, Finsupp.sum, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]`. Establish `m2 : f x0 ∈ ⨆ (x) (_ : x ≠ x0), H x`. Rewrite using `[e]`. Use `Submodule.sub_mem _ (h x0 hx0) (Submodule.sum_mem _ fun x hx => ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hx) (hf x))`.

Conclude with `(Submodule.disjoint_def.1 (hind x0)) _ (hf x0) m2`. Conclude with `Finsupp.notMem_support_iff.1 hs`. Rewrite using `[← hsum, Finsupp.sum]`. Use `Submodule.sum_mem _ fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ Y`.

Conclude with `Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx (hf x))`. Rewrite using `[h0 x hx]`. Conclude with `Submodule.zero_mem _`.
-/
theorem mem_biSup_of_forall {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (H : ι → Submodule K V)
    (hind : iSupIndep H) (htop : ⨆ x, H x = ⊤) (Y : Set ι) (v : V)
    (h : ∀ x0, x0 ∉ Y → v ∈ ⨆ (x) (_ : x ≠ x0), H x) : v ∈ ⨆ x ∈ Y, H x := by
  classical
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp H v).1 (by rw [htop]; exact Submodule.mem_top)
  have h0 : ∀ x0, x0 ∉ Y → f x0 = 0 := by
    intro x0 hx0
    by_cases hs : x0 ∈ f.support
    · have e : f x0 = v - ∑ x ∈ f.support.erase x0, f x := by
        rw [← hsum, Finsupp.sum, ← Finset.add_sum_erase _ _ hs, add_sub_cancel_right]
      have m2 : f x0 ∈ ⨆ (x) (_ : x ≠ x0), H x := by
        rw [e]
        refine Submodule.sub_mem _ (h x0 hx0) (Submodule.sum_mem _ fun x hx => ?_)
        exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem (Finset.ne_of_mem_erase hx) (hf x))
      exact (Submodule.disjoint_def.1 (hind x0)) _ (hf x0) m2
    · exact Finsupp.notMem_support_iff.1 hs
  rw [← hsum, Finsupp.sum]
  refine Submodule.sum_mem _ fun x _ => ?_
  by_cases hx : x ∈ Y
  · exact Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx (hf x))
  · rw [h0 x hx]; exact Submodule.zero_mem _

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

open Formalism.L2.NG

/- English proof (translation)
The claim follows from `D.host.φ₀.injective (by rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])`.
-/
theorem host_conj_eq (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

/- English proof (translation)
Introduce `x y hxy`. Establish `hx : (x : D.host.E) = D.host.conj (y : D.host.E)`. Rewrite using `[hxy, host_conj_eq, host_conj_eq, IsCMField.complexConj_apply_apply]`. Conclude with `(h y x hx).symm`.
-/
theorem isConjPl_symm {D : D7} {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hxy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hxy, host_conj_eq, host_conj_eq, IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

/- English proof (translation)
Introduce and unpack `⟨w', hover, hw'⟩`. Establish `hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p`. Introduce `p hp`. Establish `h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ w'.asIdeal` using `by rw [map_natCast]; exact hp`. Establish `h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal`.

Rewrite using `[← hover]`. Conclude with `h1`. Establish `h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.w.asIdeal`. Rewrite using `[← Ideal.mem_comap, s.w_under]`. Conclude with `h2`.

Rewrite `h3` using `[map_natCast]`. Conclude with `(hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by rw [host_conj_eq]; simp)).2 h3`. Take `⟨hsp, hl, hS, hQ⟩` from `hw`. Break down `hw' with hQ' | ⟨kk, hg⟩ | hpd` into its components or cases. Break down `GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w' (hover.trans s.w_under.symm) with e | e` into its components or cases.

Substitute `e` using the available equality. Conclude with `hQ (HT.Q_conj i s.w w (isConjPl_symm hc) hQ')`. Establish `ew : GlobalTheory.SplitConjPlace.conjPlE s.w = w` using `by ext1; ext x`. Rewrite using `[GlobalTheory.SplitConjPlace.mem_conjPlE]`. Use `(hc x _ ?_).symm` and prove the remaining obligations.

Rewrite using `[IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]`. Rewrite `hQ'` using `[e, ew]`. Conclude with `hQ hQ'`. Apply `hS` to reduce the goal to its premises. Use `(D.nd.S_def i w).2 ⟨?_, hl⟩` and prove the remaining obligations.

Establish `hv` using `hp _ hg`. Use `fin_cases kk`. Conclude with `Or.inl hv`. Conclude with `Or.inr (Or.inl hv)`. Conclude with `hS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr (hp _ hpd)), hl⟩)`.
-/
theorem not_bad_of_splitOut {D : D7} {M : MtFam D} (HT : HeckeTied D M) (i : D.nd.Loc) {w : PlE D.host}
    (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E) (hc : IsConjPl D.host w s.w) : s.v ∉ badPl D i := by
  rintro ⟨w', hover, hw'⟩
  have hp : ∀ p : ℕ, w' ∈ placesOver D.host.E p → w ∈ placesOver D.host.E p := by
    intro p hp
    have h1 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        w'.asIdeal := by rw [map_natCast]; exact hp
    have h2 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hover]; exact h1
    have h3 : algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) (p : 𝓞 (maximalRealSubfield D.host.E)) ∈
        s.w.asIdeal := by
      rw [← Ideal.mem_comap, s.w_under]; exact h2
    rw [map_natCast] at h3
    exact (hc (p : 𝓞 D.host.E) (p : 𝓞 D.host.E) (by rw [host_conj_eq]; simp)).2 h3
  obtain ⟨hsp, hl, hS, hQ⟩ := hw
  rcases hw' with hQ' | ⟨kk, hg⟩ | hpd
  · rcases GlobalTheory.SplitConjPlace.eq_or_eq_conjPlE s.w w' (hover.trans s.w_under.symm) with e | e
    · subst e
      exact hQ (HT.Q_conj i s.w w (isConjPl_symm hc) hQ')
    · have ew : GlobalTheory.SplitConjPlace.conjPlE s.w = w := by
        ext1; ext x
        rw [GlobalTheory.SplitConjPlace.mem_conjPlE]
        refine (hc x _ ?_).symm
        rw [IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq]
      rw [e, ew] at hQ'
      exact hQ hQ'
  · apply hS
    refine (D.nd.S_def i w).2 ⟨?_, hl⟩
    have hv := hp _ hg
    fin_cases kk
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  · exact hS ((D.nd.S_def i w).2 ⟨Or.inr (Or.inr (hp _ hpd)), hl⟩)

/- English proof (translation)
Establish `hfin` using `GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (badPl D i) (HT.J_hyp i) s ϖ k (not_bad_of_splitOut HT i hw s hc) hu`. Simplify using `only [tN]`. Rewrite using `[GlobalTheory.PtLocalEig.heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]`.
-/
theorem tN_lin {D : D7} {M : MtFam D} (HT : HeckeTied D M) (i : D.nd.Loc) {w : PlE D.host}
    (hw : SplitOut D.nd i w) (s : SplitPlace D.host.E) (hc : IsConjPl D.host w s.w)
    (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)) (hu : IsUnif D.host.E s.v ϖ) (k : ℕ) (c : ℂ)
    (f f' : GAf D.host.E D.R.nV → (M.loc i).wt.W) :
    tN (M.loc i).J s ϖ k (c • f + f') = c • tN (M.loc i).J s ϖ k f + tN (M.loc i).J s ϖ k f' := by
  have hfin := GlobalTheory.T.finite_cosets_heckeSet_at_splitPlace_outside_level D.host.E D.R.nV (M.loc i).J (M.loc i).χ (badPl D i) (HT.J_hyp i) s ϖ k
    (not_bad_of_splitOut HT i hw s hc) hu
  simp only [tN]
  rw [GlobalTheory.PtLocalEig.heckeD_add _ _ _ _ hfin c f f', smul_add, smul_comm]

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

section Hecke

variable {O X Mo : Type} [CommRing O] [IsDomain O] [AddCommGroup Mo] [Module O Mo]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O Mo)

/- English proof (translation)
Set `F : T → Module.End (FractionRing O) (TensorProduct O (FractionRing O) Mo)` to `fun f => (act f).baseChange (FractionRing O)`. Establish `hc : ∀ f g, Commute (F f) (F g)` using `fun f g => by show (act f).baseChange _ * (act g).baseChange _ = (act g).baseChange _ * (act f).baseChange _`. Rewrite using `[← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]`. Establish `h` using `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F (fun f g φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc g f) φ)`. Set `χ : X → (T → FractionRing O)` to `fun x f => algebraMap O (FractionRing O) ((f : X → O) x)`.

Establish `hχ : Function.Injective χ`. Introduce `x y hxy`. Assume the negation of the conclusion as `hne`. Take `⟨f, hf, hfx⟩` from `hsep x y hne`. Conclude with `hfx (IsFractionRing.injective O (FractionRing O) (congrFun hxy ⟨f, hf⟩))`.

Use `(h.comp hχ).mono fun x => iInf_mono fun f => ?_` and prove the remaining obligations. Conclude with `((F f).eigenspace_le_genEigenspace (k := 1) (by norm_num)).trans (((F f).genEigenspace _).monotone le_top)`.
-/
theorem heckeEig_iSupIndep (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) :
    iSupIndep (heckeEig T act) := by
  let F : T → Module.End (FractionRing O) (TensorProduct O (FractionRing O) Mo) :=
    fun f => (act f).baseChange (FractionRing O)
  have hc : ∀ f g, Commute (F f) (F g) := fun f g => by
    show (act f).baseChange _ * (act g).baseChange _ = (act g).baseChange _ * (act f).baseChange _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, ← map_mul, ← map_mul, mul_comm]
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo F
    (fun f g φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc g f) φ)
  let χ : X → (T → FractionRing O) := fun x f => algebraMap O (FractionRing O) ((f : X → O) x)
  have hχ : Function.Injective χ := by
    intro x y hxy
    by_contra hne
    obtain ⟨f, hf, hfx⟩ := hsep x y hne
    exact hfx (IsFractionRing.injective O (FractionRing O) (congrFun hxy ⟨f, hf⟩))
  refine (h.comp hχ).mono fun x => iInf_mono fun f => ?_
  exact ((F f).eigenspace_le_genEigenspace (k := 1) (by norm_num)).trans
    (((F f).genEigenspace _).monotone le_top)

/- English proof (translation)
Establish `hu : u ∈ ⨆ x, heckeEig T act x` using `by rw [htop]; exact Submodule.mem_top`. Use `Submodule.iSup_induction (heckeEig T act) (motive := fun u => φ ((act f).baseChange (FractionRing O) u) = algebraMap O (FractionRing O) ((f : X → O) x0) * φ u) hu ?_ ?_ ?_` and prove the remaining obligations. Introduce `x u hux`. Establish `he : (act f).baseChange (FractionRing O) u = algebraMap O (FractionRing O) ((f : X → O) x) • u` using `Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hux f)`. Rewrite using `[he, map_smul, smul_eq_mul]`.

Distinguish the cases in `hx : x = x0`. Rewrite using `[hx]`. Rewrite using `[hφ x hx u hux, mul_zero, mul_zero]`. Simplify using the standard rewrite rules. Introduce `a b ha hb`.

Rewrite using `[map_add, map_add, map_add, ha, hb, mul_add]`.
-/
theorem dual_eig (htop : ⨆ x, heckeEig T act x = ⊤) (x0 : X)
    (φ : Module.Dual (FractionRing O) (TensorProduct O (FractionRing O) Mo))
    (hφ : ∀ x, x ≠ x0 → ∀ u ∈ heckeEig T act x, φ u = 0) (f : T) (u : TensorProduct O (FractionRing O) Mo) :
    φ ((act f).baseChange (FractionRing O) u) = algebraMap O (FractionRing O) ((f : X → O) x0) * φ u := by
  have hu : u ∈ ⨆ x, heckeEig T act x := by rw [htop]; exact Submodule.mem_top
  refine Submodule.iSup_induction (heckeEig T act)
    (motive := fun u => φ ((act f).baseChange (FractionRing O) u) = algebraMap O (FractionRing O) ((f : X → O) x0) * φ u)
    hu ?_ ?_ ?_
  · intro x u hux
    have he : (act f).baseChange (FractionRing O) u = algebraMap O (FractionRing O) ((f : X → O) x) • u :=
      Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hux f)
    rw [he, map_smul, smul_eq_mul]
    by_cases hx : x = x0
    · rw [hx]
    · rw [hφ x hx u hux, mul_zero, mul_zero]
  · simp
  · intro a b ha hb; rw [map_add, map_add, map_add, ha, hb, mul_add]

end Hecke

end GlobalTheory.EtaJoin.TypeTieProof

namespace GlobalTheory.EtaJoin.TypeTieProof

open Formalism.L2.NG

/- English proof (translation)
Introduce `D M i HT HR AV _ HS HE S y hy`. Set `ι : FractionRing (D.nd.O i) →+* ℂ` to `(D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)`. Establish `hι : ∀ a, ι (D.nd.embK i a) = D.what₂.embLL a` using `D.naut.iota_LL i`. Use `mem_biSup_of_forall (heckeEig (D.nd.T i) (D.nd.act i)) (heckeEig_iSupIndep _ _ (D.nd.T_sep i)) (HE i) {x | ∃ P ∈ S, D.naut.ptV i P = some x} _ ?_` and prove the remaining obligations. Introduce `x0 hx0`.

Assume the negation of the conclusion as `hv`. Take `⟨φ, hφv, hφB⟩` from `Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance`. Establish `hφ0 : ∀ x, x ≠ x0 → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, φ u = 0`. Introduce `x hx u hu`. Establish `hm : φ u ∈ Submodule.map φ (⨆ (x) (_ : x ≠ x0), heckeEig (D.nd.T i) (D.nd.act i) x)` using `Submodule.mem_map_of_mem (Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx hu))`.

Rewrite `hm` using `[hφB]`. Conclude with `(Submodule.mem_bot _).1 hm`. Establish `hφe` using `dual_eig (D.nd.T i) (D.nd.act i) (HE i) x0 φ hφ0`. Set `b` to `Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))`. Establish `hb` using `D.what₂.jMt_basis (D.nd.mu i) (D.nd.j i) b`.

Set `f0 : D.what₂.MtL (D.nd.mu i) (D.nd.j i) →ₛₗ[D.what₂.embLL] ℂ` to `{ toFun := fun z => ι (φ (D.nd.prMt i z)) map_add' := fun a c => by simp only [map_add] map_smul' := fun a z => by show ι (φ (D.nd.prMt i (a • z))) = D.what₂.embLL a • ι (φ (D.nd.prMt i z))`. Rewrite using `[LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, hι, smul_eq_mul] }`. Take `⟨Ψ, hΨ⟩` from `exists_ext_semilin D.what₂.embLL (D.what₂.jMt _ _) b hb.1 hb.2 f0`. Set `bC : Module.Basis _ ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i))` to `Module.Basis.mk hb.1 hb.2.ge`. Establish `hbC : ∀ q, bC q = D.what₂.jMt _ _ (b q)` using `fun q => by simp [bC]`.

Establish `hker : ∀ P ∈ S, D.naut.typeV i P ≤ LinearMap.ker Ψ`. Introduce `P hP z hz`. Assume the negation of the conclusion as `hz0`. Rewrite `hz0` using `[LinearMap.mem_ker]`. Apply `hx0` to reduce the goal to its premises.

Use `⟨P, hP, (AV.ptV i P x0).2 ?_⟩` and prove the remaining obligations. Introduce `w k s ϖ hw hc hu hk1 hk2 y' hy'`. Take `⟨c, hcP⟩` from `HS P w k s ϖ hw hc hu hk1 hk2`. Use `choose x' hx' using HR i w k s ϖ hw hc hu hk1 hk2`. Set `Tt : Module.End ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i))` to `bC.constr ℂ (fun q => D.what₂.jMt _ _ (x' (b q)))`.

Establish `hTb : ∀ q, Tt (bC q) = D.what₂.jMt _ _ (x' (b q))` using `fun q => by`. Simplify using `only [Tt, Module.Basis.constr_basis]`. Establish `t0 : tN (M.loc i).J s ϖ k (0 : GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0`. Establish `e` using `tN_lin HT i hw s hc ϖ hu k 1 0 0`. Simplify using `only [smul_zero, add_zero, one_smul] at e`.

Simplify using `using e`. Set `tl : (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ[ℂ] (GAf D.host.E D.R.nV → (M.loc i).wt.W)` to `{ toFun := tN (M.loc i).J s ϖ k map_add' := fun f f' => by simpa using tN_lin HT i hw s hc ϖ hu k 1 f f' map_smul' := fun a f => by simpa [t0] using tN_lin HT i hw s hc ϖ hu k a f 0 }`. Establish `hreal : (M.loc i).real ∘ₗ Tt = tl ∘ₗ (M.loc i).real` using `bC.ext fun q => by`. Rewrite using `[LinearMap.comp_apply, LinearMap.comp_apply, hTb, hbC]`. Conclude with `hx' (b q)`.

Establish `hΨT : Ψ ∘ₗ Tt = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) • Ψ` using `bC.ext fun q => by`. Rewrite using `[LinearMap.comp_apply, hTb, LinearMap.smul_apply, hbC, hΨ, hΨ]`. Use `show ι (φ (D.nd.prMt i (x' (b q)))) = _ • ι (φ (D.nd.prMt i (b q)))`. Rewrite using `[HT.hT i w k s ϖ hw hc hu hk1 hk2 (b q) (x' (b q)) (hx' (b q)), hφe, map_mul, smul_eq_mul]`. Establish `hTz : Tt z = c • z` using `(M.loc i).real_inj (by`.

Establish `e` using `LinearMap.congr_fun hreal z`. Rewrite `e` using `[LinearMap.comp_apply, LinearMap.comp_apply]`. Rewrite using `[e, map_smul]`. Conclude with `hcP z hz)`. Establish `hcz : c = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0))`.

Establish `e` using `LinearMap.congr_fun hΨT z`. Rewrite `e` using `[LinearMap.comp_apply, LinearMap.smul_apply, hTz, map_smul, smul_eq_mul, smul_eq_mul]`. Conclude with `mul_right_cancel₀ hz0 e`. Rewrite using `[hcP y' hy', hcz]`. Both sides reduce to the same expression.

Establish `hyk` using `(iSup₂_le hker) hy`. Rewrite `hyk` using `[LinearMap.mem_ker, hΨ]`. Conclude with `hφv ((map_eq_zero_iff ι ι.injective).1 hyk)`.
-/
theorem typeTie_holds : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M →
    SplitUnif D → HeckeScalar M i → D.nd.EigSpan → TypeTie D i := by
  intro D M i HT HR AV _ HS HE S y hy
  classical
  let ι : FractionRing (D.nd.O i) →+* ℂ := (D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)
  have hι : ∀ a, ι (D.nd.embK i a) = D.what₂.embLL a := D.naut.iota_LL i
  refine mem_biSup_of_forall (heckeEig (D.nd.T i) (D.nd.act i))
    (heckeEig_iSupIndep _ _ (D.nd.T_sep i)) (HE i) {x | ∃ P ∈ S, D.naut.ptV i P = some x} _ ?_
  intro x0 hx0
  by_contra hv
  obtain ⟨φ, hφv, hφB⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hφ0 : ∀ x, x ≠ x0 → ∀ u ∈ heckeEig (D.nd.T i) (D.nd.act i) x, φ u = 0 := by
    intro x hx u hu
    have hm : φ u ∈ Submodule.map φ (⨆ (x) (_ : x ≠ x0), heckeEig (D.nd.T i) (D.nd.act i) x) :=
      Submodule.mem_map_of_mem (Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx hu))
    rw [hφB] at hm
    exact (Submodule.mem_bot _).1 hm
  have hφe := dual_eig (D.nd.T i) (D.nd.act i) (HE i) x0 φ hφ0
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (D.nd.mu i) (D.nd.j i))
  have hb := D.what₂.jMt_basis (D.nd.mu i) (D.nd.j i) b
  let f0 : D.what₂.MtL (D.nd.mu i) (D.nd.j i) →ₛₗ[D.what₂.embLL] ℂ :=
    { toFun := fun z => ι (φ (D.nd.prMt i z))
      map_add' := fun a c => by simp only [map_add]
      map_smul' := fun a z => by
        show ι (φ (D.nd.prMt i (a • z))) = D.what₂.embLL a • ι (φ (D.nd.prMt i z))
        rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, hι, smul_eq_mul] }
  obtain ⟨Ψ, hΨ⟩ := exists_ext_semilin D.what₂.embLL (D.what₂.jMt _ _) b hb.1 hb.2 f0
  let bC : Module.Basis _ ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := Module.Basis.mk hb.1 hb.2.ge
  have hbC : ∀ q, bC q = D.what₂.jMt _ _ (b q) := fun q => by simp [bC]
  have hker : ∀ P ∈ S, D.naut.typeV i P ≤ LinearMap.ker Ψ := by
    intro P hP z hz
    by_contra hz0
    rw [LinearMap.mem_ker] at hz0
    apply hx0
    refine ⟨P, hP, (AV.ptV i P x0).2 ?_⟩
    intro w k s ϖ hw hc hu hk1 hk2 y' hy'
    obtain ⟨c, hcP⟩ := HS P w k s ϖ hw hc hu hk1 hk2
    choose x' hx' using HR i w k s ϖ hw hc hu hk1 hk2
    let Tt : Module.End ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
      bC.constr ℂ (fun q => D.what₂.jMt _ _ (x' (b q)))
    have hTb : ∀ q, Tt (bC q) = D.what₂.jMt _ _ (x' (b q)) := fun q => by
      simp only [Tt, Module.Basis.constr_basis]
    have t0 : tN (M.loc i).J s ϖ k (0 : GAf D.host.E D.R.nV → (M.loc i).wt.W) = 0 := by
      have e := tN_lin HT i hw s hc ϖ hu k 1 0 0
      simp only [smul_zero, add_zero, one_smul] at e
      simpa using e
    let tl : (GAf D.host.E D.R.nV → (M.loc i).wt.W) →ₗ[ℂ] (GAf D.host.E D.R.nV → (M.loc i).wt.W) :=
      { toFun := tN (M.loc i).J s ϖ k
        map_add' := fun f f' => by simpa using tN_lin HT i hw s hc ϖ hu k 1 f f'
        map_smul' := fun a f => by simpa [t0] using tN_lin HT i hw s hc ϖ hu k a f 0 }
    have hreal : (M.loc i).real ∘ₗ Tt = tl ∘ₗ (M.loc i).real := bC.ext fun q => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hTb, hbC]
      exact hx' (b q)
    have hΨT : Ψ ∘ₗ Tt = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) • Ψ :=
      bC.ext fun q => by
        rw [LinearMap.comp_apply, hTb, LinearMap.smul_apply, hbC, hΨ, hΨ]
        show ι (φ (D.nd.prMt i (x' (b q)))) = _ • ι (φ (D.nd.prMt i (b q)))
        rw [HT.hT i w k s ϖ hw hc hu hk1 hk2 (b q) (x' (b q)) (hx' (b q)), hφe, map_mul, smul_eq_mul]
    have hTz : Tt z = c • z := (M.loc i).real_inj (by
      have e := LinearMap.congr_fun hreal z
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at e
      rw [e, map_smul]
      exact hcP z hz)
    have hcz : c = ι (algebraMap _ (FractionRing (D.nd.O i)) ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x0)) := by
      have e := LinearMap.congr_fun hΨT z
      rw [LinearMap.comp_apply, LinearMap.smul_apply, hTz, map_smul, smul_eq_mul, smul_eq_mul] at e
      exact mul_right_cancel₀ hz0 e
    rw [hcP y' hy', hcz]
    rfl
  have hyk := (iSup₂_le hker) hy
  rw [LinearMap.mem_ker, hΨ] at hyk
  exact hφv ((map_eq_zero_iff ι ι.injective).1 hyk)

end GlobalTheory.EtaJoin.TypeTieProof
