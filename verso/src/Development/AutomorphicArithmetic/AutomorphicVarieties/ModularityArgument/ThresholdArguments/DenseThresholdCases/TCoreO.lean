import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.MapOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THasOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocalLanglandsGLOfPrints

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Th
namespace UpperTheory.V.Th.NormTraceLemmas
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
/- English proof (translation)
Take `⟨hc, hf, hlm, -, -, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Use `⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩` and prove the remaining obligations. Rewrite using `[← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]`. Conclude with `hlm`.
-/
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : HV.Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
/- English proof (translation)
Assemble the required witnesses or components as `⟨P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩`.
-/
private theorem locP_of (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : _root_.UpperTheory.V.Pa.LocPAlt :=
  ⟨P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩
/- English proof (translation)
Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ (Polynomial A) _).det = _`. Rewrite using `[map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]`. Use `congr 1`. Use extensionality with `i j : 2`. Apply the tactic sequence `by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]`.
-/
private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]
/- English proof (translation)
Use `GDet.ext fun C _ _ x => ?_` and prove the remaining obligations. Use `letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra`. Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det`. Use `congr 2`.
-/
private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2
/- English proof (translation)
Establish `hl : l.Prime` using `Fact.out`. Use `haveI : Nonempty (Fin n) := ⟨i⟩`. Establish `h0` using `Matrix.aeval_self_charpoly (M.map (residue O))`. Rewrite `h0` using `[hM]`. Simplify using `only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h0`.

Establish `h1 : (residue O).mapMatrix (M ^ l ^ n) = 1`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (Nat.lt_pow_self hl.one_lt (n := n)).le`. Establish `h4` using `sub_pow_char_pow_of_commute l n (Commute.one_right (M.map (residue O)))`. Rewrite `h4` using `[one_pow]`. Rewrite using `[map_pow, ← sub_eq_zero]`.

Use `h4.symm.trans ?_` and prove the remaining obligations. Rewrite using `[hd, pow_add, h0, zero_mul]`. Establish `h2 : ∀ k, (residue O).mapMatrix (M ^ l ^ (n + k)) = 1` using `fun k => by`. Rewrite using `[pow_add, pow_mul, map_pow, h1, one_pow]`. Proceed by induction on `m generalizing i j with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[← add_assoc, pow_succ l, pow_mul, ← mul_geom_sum, Matrix.mul_apply, pow_succ]`. Use `Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih i a) ?_` and prove the remaining obligations. Establish `h3 : (residue O).mapMatrix (∑ t ∈ Finset.range l, (M ^ l ^ (n + k)) ^ t) = 0`.

Simplify using `only [map_sum, map_pow (residue O).mapMatrix (M ^ l ^ (n + k)), h2, one_pow]`. Simplify using the standard rewrite rules. Conclude with `(residue_eq_zero_iff _).1 (congrFun (congrFun h3 a) j)`.
-/
private theorem unip_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (hM : (M.map (residue O)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n + m) - 1) i j ∈ maximalIdeal O ^ m := by
  have hl : l.Prime := Fact.out
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h0 := Matrix.aeval_self_charpoly (M.map (residue O))
  rw [hM] at h0
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h0
  have h1 : (residue O).mapMatrix (M ^ l ^ n) = 1 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self hl.one_lt (n := n)).le
    have h4 := sub_pow_char_pow_of_commute l n (Commute.one_right (M.map (residue O)))
    rw [one_pow] at h4
    rw [map_pow, ← sub_eq_zero]
    refine h4.symm.trans ?_
    rw [hd, pow_add, h0, zero_mul]
  have h2 : ∀ k, (residue O).mapMatrix (M ^ l ^ (n + k)) = 1 := fun k => by
    rw [pow_add, pow_mul, map_pow, h1, one_pow]
  induction m generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ l, pow_mul, ← mul_geom_sum, Matrix.mul_apply, pow_succ]
    refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih i a) ?_
    have h3 : (residue O).mapMatrix (∑ t ∈ Finset.range l, (M ^ l ^ (n + k)) ^ t) = 0 := by
      simp only [map_sum, map_pow (residue O).mapMatrix (M ^ l ^ (n + k)), h2, one_pow]
      simp
    exact (residue_eq_zero_iff _).1 (congrFun (congrFun h3 a) j)
/- English proof (translation)
Establish `key : ∀ (m : ℕ) (i j : Fin n), (mat ρ g - 1) i j ∈ maximalIdeal O ^ m`. Introduce `m`. Set `π` to `Ideal.Quotient.mk (maximalIdeal O ^ m)`. Set `Km : Subgroup F.G₀` to `(π.mapMatrix.toMonoidHom.comp (mat ρ)).toHomUnits.ker`. Establish `hKm : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j)`.

Introduce `a`. Rewrite using `[MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one, ← map_one π.mapMatrix, ← Matrix.ext_iff]`. Both sides reduce to the same expression. Establish `hKm' : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, (mat ρ a - 1) i j ∈ maximalIdeal O ^ m`. Introduce `a`.

Simplify using `only [hKm, Matrix.sub_apply, π, Ideal.Quotient.eq]`. Establish `ho : IsOpen (Km : Set F.G₀)`. Establish `: (Km : Set F.G₀) = ⋂ i, ⋂ j, {a | π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j)}`. Use extensionality with `a`. Simplify using `only [SetLike.mem_coe, hKm, Set.mem_iInter, Set.mem_setOf_eq]`.

Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hc i j m).isOpen_fiber _`. Set `K' : Subgroup F.Γ` to `Km.map F.η.ker.subtype`. Establish `ho' : IsOpen (K' : Set F.Γ)` using `F.η_open.isOpenMap_subtype_val _ ho`. Use `haveI : Finite (F.Γ ⧸ K') := Subgroup.quotient_finite_of_isOpen K' ho'`.

Use `haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Establish `hc : IsOpen (K'.normalCore : Set F.Γ)` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K'.normalCore_isClosed (K'.isClosed_of_isOpen ho'))`. Set `U : OpenNormalSubgroup F.Γ` to `⟨⟨K'.normalCore, hc⟩, K'.normalCore_normal⟩`. Establish `hU : ∀ h ∈ H.toSubgroup, ∃ e : ℕ, h ^ l ^ e ∈ U`. Introduce `h hh`.

Use `⟨n + m, fun b => ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `hH (b * h * b⁻¹) (H.isNormal'.conj_mem h hh b)`. Use `⟨(⟨b * h * b⁻¹, h1⟩ : F.G₀) ^ l ^ (n + m), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, hKm', map_pow]`. Conclude with `unip_pow l O n m _ h2`.

Simplify using `only [Subgroup.coe_subtype, SubgroupClass.coe_pow, conj_pow]`. Establish `h3 : (g : F.Γ) ∈ K'.normalCore` using `Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg U) hU`. Take `⟨a, ha, hag⟩` from `K'.normalCore_le h3`. Take `rfl : a = g` from `Subtype.ext hag`. Conclude with `(hKm' a).1 ha`.

Apply `Units.ext` to reduce the goal to its premises. Use `ext1 i j`. Establish `h0 : (mat ρ g - 1) i j ∈ (⨅ m : ℕ, maximalIdeal O ^ m)` using `Ideal.mem_iInf.2 fun m => key m i j`. Rewrite `h0` using `[Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot, Matrix.sub_apply, sub_eq_zero]`. Conclude with `h0`.
-/
private theorem rhoPLO (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CharP (ResidueField O) l] (n : ℕ) (ρ : F.G₀ →* GL (Fin n) O)
    (hc : ∀ i j, AdicCont (maximalIdeal O) fun g => mat ρ g i j) (H : OpenNormalSubgroup F.Γ)
    (hH : ∀ g ∈ H, ∃ h : F.η g = 1, ((mat ρ ⟨g, h⟩).map (residue O)).charpoly = (Polynomial.X - 1) ^ n)
    (g : F.G₀) (hg : (g : F.Γ) ∈ PL l H.toSubgroup) : ρ g = 1 := by
  have key : ∀ (m : ℕ) (i j : Fin n), (mat ρ g - 1) i j ∈ maximalIdeal O ^ m := by
    intro m
    let π := Ideal.Quotient.mk (maximalIdeal O ^ m)
    let Km : Subgroup F.G₀ := (π.mapMatrix.toMonoidHom.comp (mat ρ)).toHomUnits.ker
    have hKm : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j) := by
      intro a
      rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one, ← map_one π.mapMatrix,
        ← Matrix.ext_iff]
      rfl
    have hKm' : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, (mat ρ a - 1) i j ∈ maximalIdeal O ^ m := by
      intro a
      simp only [hKm, Matrix.sub_apply, π, Ideal.Quotient.eq]
    have ho : IsOpen (Km : Set F.G₀) := by
      have : (Km : Set F.G₀) = ⋂ i, ⋂ j, {a | π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j)} := by
        ext a
        simp only [SetLike.mem_coe, hKm, Set.mem_iInter, Set.mem_setOf_eq]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hc i j m).isOpen_fiber _
    let K' : Subgroup F.Γ := Km.map F.η.ker.subtype
    have ho' : IsOpen (K' : Set F.Γ) := F.η_open.isOpenMap_subtype_val _ ho
    haveI : Finite (F.Γ ⧸ K') := Subgroup.quotient_finite_of_isOpen K' ho'
    haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hc : IsOpen (K'.normalCore : Set F.Γ) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K'.normalCore_isClosed (K'.isClosed_of_isOpen ho'))
    let U : OpenNormalSubgroup F.Γ := ⟨⟨K'.normalCore, hc⟩, K'.normalCore_normal⟩
    have hU : ∀ h ∈ H.toSubgroup, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨n + m, fun b => ?_⟩
      obtain ⟨h1, h2⟩ := hH (b * h * b⁻¹) (H.isNormal'.conj_mem h hh b)
      refine ⟨(⟨b * h * b⁻¹, h1⟩ : F.G₀) ^ l ^ (n + m), ?_, ?_⟩
      · rw [SetLike.mem_coe, hKm', map_pow]
        exact unip_pow l O n m _ h2
      · simp only [Subgroup.coe_subtype, SubgroupClass.coe_pow, conj_pow]
    have h3 : (g : F.Γ) ∈ K'.normalCore := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg U) hU
    obtain ⟨a, ha, hag⟩ := K'.normalCore_le h3
    obtain rfl : a = g := Subtype.ext hag
    exact (hKm' a).1 ha
  apply Units.ext
  ext1 i j
  have h0 : (mat ρ g - 1) i j ∈ (⨅ m : ℕ, maximalIdeal O ^ m) := Ideal.mem_iInf.2 fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot, Matrix.sub_apply,
    sub_eq_zero] at h0
  exact h0
/- English proof (translation)
Establish `e0 : (residue O).comp x.toRingHom = (res O B : B →+* ResidueField O)` using `RingHom.ext fun a => ((res O O).commutes (x a)).symm.trans (res_map x a)`. Establish `e3 : (GDet.ofRep (mat ρ)).map (residue O) = r.Dbar`. Rewrite using `[← h, ← u.red, ← e0]`. Both sides reduce to the same expression. Rewrite `e3` using `[map_ofRep, Resid.Dbar]`.

Establish `e4` using `congrArg (·.chi (MonoidAlgebra.single g 1)) e3`. Simplify using `only [chi_ofRep] at e4`. Use `e4.trans ?_` and prove the remaining obligations. Establish `e5 : W.diagRep r.chib g = 1`. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ = _`.

Simplify using `only [hg, Units.val_one, Matrix.diagonal_one]`. Rewrite using `[e5, Matrix.charpoly_one, Fintype.card_fin]`.
-/
private theorem red_unip {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (x : B →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (h : u.D.map x.toRingHom = GDet.ofRep (mat ρ))
    (g : F.G₀) (hg : ∀ i, r.chib i g = 1) : ((mat ρ g).map (residue O)).charpoly = (Polynomial.X - 1) ^ n := by
  have e0 : (residue O).comp x.toRingHom = (res O B : B →+* ResidueField O) := RingHom.ext fun a =>
    ((res O O).commutes (x a)).symm.trans (res_map x a)
  have e3 : (GDet.ofRep (mat ρ)).map (residue O) = r.Dbar := by
    rw [← h, ← u.red, ← e0]
    rfl
  rw [map_ofRep, Resid.Dbar] at e3
  have e4 := congrArg (·.chi (MonoidAlgebra.single g 1)) e3
  simp only [chi_ofRep] at e4
  refine e4.trans ?_
  have e5 : W.diagRep r.chib g = 1 := by
    change Matrix.diagonal _ = _
    simp only [hg, Units.val_one, Matrix.diagonal_one]
  rw [e5, Matrix.charpoly_one, Fintype.card_fin]
end UpperTheory.V.Th.NormTraceLemmas
open UpperTheory.V.Th.NormTraceLemmas UpperTheory.V.Pa UpperTheory.V.W UpperTheory.V.Alg in
/- English proof (translation)
Introduce `hN l _ L Ω _ _ _ _ _ _ s V0 c n r B J y x h q sg al hS hn hLev hJ hAr hmap hN4 hsg hdet δ hδ h0`. Establish `hC : Pa.CohP` using `⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩`. Use `haveI := coef_isCoef l c`. Use `haveI := IsCoef.char (l := l) (O := c.O)`. Use `haveI := IsCoef.finite (l := l) (O := c.O)`.

Use `haveI := IsCoef.complete (l := l) (O := c.O)`. Take `⟨b, hb, hγ, hctrl⟩` from `hLev`. Take `⟨T, ⟨Pl⟩, rfl, hTs⟩` from `(arPl hC l L Ω s V0 c.O n r hS).2 q sg fun j => (hsg j).1`. Take `rfl : T.sg = sg` from `funext hTs`. Establish `hI` using `(ipEq l L Ω s V0 c.O n r).1`.

Establish `hgen : GenBy c.O (pairVals (pairOf B.u))` using `fun N b => by`. Take `⟨c, hc, hb⟩` from `CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b`. Use `⟨c, Algebra.adjoin_mono ?_ hc, hb⟩` and prove the remaining obligations. Introduce and unpack `_ (⟨a, g, -, -, rfl⟩ | e)`. Conclude with `Or.inl ⟨a, g, rfl⟩`.

Conclude with `Or.inr e`. Establish `hmap' : (pairOf B.u).Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ` using `hmap`. Establish `hker : ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1`. Use `rhoPLO l (globOf r V0).frame c.O n y.ρ y.cont T.H fun g hg => ?_` and prove the remaining obligations. Take `⟨e1, e2, -⟩` from `(Pl.H_eq g).1 hg`.

Conclude with `⟨e1, red_unip (pairOf B.u) x y.ρ hmap'.1 ⟨g, e1⟩ e2⟩`. Establish `heig : Eig y T al` using `fun j => (hsg j).2`. Conclude with `count l _ (globOf r V0) T n c.O (residOf r) B.B (pairOf B.u) J _ b y x al s.odd hn ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩ (_root_.UpperTheory.V.Th.has_operator_statement (locP_of hN) l L Ω s V0 c.O n r B J _ b hb T Pl) hgen hmap' hJ (etOf l _ (globOf r V0) n …`.
-/
theorem UpperTheory.V.Th.core_o_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Th.OrdinaryMainCase := by
  intro hN l _ L Ω _ _ _ _ _ _ s V0 c n r B J y x h q sg al hS hn hLev hJ hAr hmap hN4 hsg hdet δ hδ h0
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  haveI := coef_isCoef l c
  haveI := IsCoef.char (l := l) (O := c.O)
  haveI := IsCoef.finite (l := l) (O := c.O)
  haveI := IsCoef.complete (l := l) (O := c.O)
  obtain ⟨b, hb, hγ, hctrl⟩ := hLev
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := (arPl hC l L Ω s V0 c.O n r hS).2 q sg fun j => (hsg j).1
  obtain rfl : T.sg = sg := funext hTs
  have hI := (ipEq l L Ω s V0 c.O n r).1
  have hgen : GenBy c.O (pairVals (pairOf B.u)) := fun N b => by
    obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
    refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
    rintro _ (⟨a, g, -, -, rfl⟩ | e)
    · exact Or.inl ⟨a, g, rfl⟩
    · exact Or.inr e
  have hmap' : (pairOf B.u).Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ := hmap
  have hker : ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1 := by
    refine rhoPLO l (globOf r V0).frame c.O n y.ρ y.cont T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    exact ⟨e1, red_unip (pairOf B.u) x y.ρ hmap'.1 ⟨g, e1⟩ e2⟩
  have heig : Eig y T al := fun j => (hsg j).2
  exact count l _ (globOf r V0) T n c.O (residOf r) B.B (pairOf B.u) J _ b y x al s.odd hn
    ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
    (_root_.UpperTheory.V.Th.has_operator_statement (locP_of hN) l L Ω s V0 c.O n r B J _ b hb T Pl) hgen hmap' hJ
    (etOf l _ (globOf r V0) n c.O (residOf r) B.B (pairOf B.u) J _ b y x hn hmap' hgen (hctrl x h hAr)) hker heig
    (b1O hC l L Ω s V0 c n r T Pl y al hS (W.locCFT hN.aut.art hC l L Ω s) hn hker hN4 heig hdet)
    δ hδ fun k => h0 _ _ _ (hγ k)
end
