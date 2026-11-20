import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslateLocallyNoetherianBaseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateWeilLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenModelEqGenericFibre

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `a.add 0 0`. Rewrite `h` using `[add_zero]`. Establish `h2` using `congrArg (· * (a.act 0)⁻¹) h`.

Simplify using `only [mul_inv_cancel, mul_inv_cancel_right] at h2`. Rewrite using `[Nat.cast_zero, pow_zero]`. Conclude with `h2.symm`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ, a.add, ih, a.one, pow_succ]`.
-/
private theorem oActN_act_natCast_eq_one_pow {S : Scheme} {O : Type} [Ring O] {G : Over S} [GrpObj G]
    (a : GlobalTheory.UPel.HT.OActN O G) (n : ℕ) : a.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    have h2 := congrArg (· * (a.act 0)⁻¹) h
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h2
    rw [Nat.cast_zero, pow_zero]
    exact h2.symm
  | succ n ih =>
    rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

/- English proof (translation)
Introduce `hSys hAdm hFull hRel p _ D G L R _ _ gb h hI`. Take `⟨f, u, c, k, hsys, hm, hk, hf⟩` from `hSys p D G L h hI`. Take `⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩` from `hsys`. Establish `hk0 : 0 < k`. Break down `Nat.eq_zero_or_pos k with rfl | hpos` into its components or cases.

Conclude with `absurd (Nat.coprime_zero_left p |>.mp hkp) (Fact.out : Nat.Prime p).one_lt.ne'`. Conclude with `hpos`. Use `⟨k, hkp, fun N => hAdm p D G L h k N hI hk0 hk, ?_⟩` and prove the remaining obligations. Introduce `N S _ s o'`. Establish `hρ : gb.ρ = (RingHom.id R) (GenCmp.baseOf gb).ρ` using `rfl`.

Establish `ht : ∀ i, gb.t i = (RingHom.id R).comp ((GenCmp.baseOf gb).t i)` using `fun i => rfl`. Set `o1` to `GenCmp.toObj hρ ht o' (GenCmp.genericObject_kernelCondition o')`. Take `⟨o2, ψ, hψm, hψa, hψe, hgal, ⟨hlb⟩, -⟩` from `GlobalTheory.T.exists_hecke_translate_locallyNoetherian_base p D R (GenCmp.baseOf gb) f u c k N N.2.1 N.2.2 hc hkp hck hlin hcomp hEF hsurj S _ o1`. Set `o3` to `GenCmp.rebase (t := s) hρ ht rfl o2`. Set `o : GObj gb N s` to `GenCmp.toGObj o3 (GenCmp.geomFull N.2.2 o3)`.

Use `⟨o, ψ, ?_⟩` and prove the remaining obligations. Unfold `UpperTheory.Gal.Int.Geo.IsTrans`. Use `haveI := hψm`. Use `haveI : Epi (Over.Hom.left ψ) := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal`. Use `haveI : Epi ψ := Over.epi_of_epi_left ψ`.

Take `⟨ψ', hψ'm, hψψ'⟩` from `GlobalTheory.HomDescent.exists_desc S o1.A o2.A o1.A (HeckeAd.heckeSubA o1 (f (↑N * k)) ↑N) ψ hψm hgal (o1.act.act (k : D.O)) (o1.act.hom _) (fun g hg => by`. Rewrite using `[oActN_act_natCast_eq_one_pow, comp_pow, Category.comp_id, HeckeAd.pow_eq_one_of_mem o1 _ g hg])`. Use `⟨hψm, hψa, ⟨ψ', k, hψ'm, ?_, ?_, ?_, hkp⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Express the relevant statement in the definitionally equal form `o2.act.act a ≫ ψ' = ψ' ≫ o1.act.act a`.

Apply `(cancel_epi ψ).1` to reduce the goal to its premises. Rewrite using `[← Category.assoc, ← hψa a, Category.assoc, hψψ', ← Category.assoc, hψψ', ← o1.act.mul, ← o1.act.mul, Nat.cast_comm]`. Express the relevant statement in the definitionally equal form `ψ ≫ ψ' = 𝟙 o1.A ^ k`. Rewrite using `[hψψ', oActN_act_natCast_eq_one_pow]`. Express the relevant statement in the definitionally equal form `ψ' ≫ ψ = 𝟙 o2.A ^ k`.

Apply `(cancel_epi ψ).1` to reduce the goal to its premises. Rewrite using `[← Category.assoc, hψψ', oActN_act_natCast_eq_one_pow, pow_comp, comp_pow, Category.id_comp, Category.comp_id]`. Take `⟨t, t', ht1, ht2, ht3, ht4⟩` from `hm`. Conclude with `⟨k ^ 2 / c, Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (Nat.Coprime.pow_left 2 hkp), ⟨hlb⟩, t, t', ht1, ht2, ht3, ht4⟩`. Introduce `kk _ _ t β htβ`.

Take `⟨I', hI'⟩` from `o'.geom kk t β htβ`. Take `⟨J0, hJ0e, hJ0r⟩` from `HeckeAd.TateTranslAt.exists_tateIsoO_of_given D (GenCmp.baseOf gb) f u c k N hc hkp N.2.1 N.2.2 hck hlin hcomp hEF hsurj o1 o2.A o2.act ψ o2.ab hψm hgal hψa o2.P o2.isLB hlb kk t β (GenCmp.tateRestrict I') (fun y => hI' y)`. Take `⟨I'', hI''⟩` from `hFull p D R gb S s N o kk t J0`. Establish `hNpos : 0 < (N : ℕ)` using `lt_of_lt_of_le (by norm_num) N.2.1`. Use `⟨I', I'', hI', fun y => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hI'' _ hNpos N.2.2, ← hJ0e y]`. Express the relevant statement in the definitionally equal form `toUnit (Over.mk t) ≫ o2.eta y = _`. Rewrite using `[hψe y]`. Conclude with `hRel p D G L R gb S s N (↑N * k) o' o kk t I' I'' ψ h f u c k hψm hI ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ hf (fun n hn hnp x => by rw [hI'' n hn hnp]; exact hJ0r n hn hnp x)`.
-/
theorem UpperTheory.Gal.G3.pTransDeep :
    SysOf → AdmOf → FullOf → RelArith → TransDeep := by
  intro hSys hAdm hFull hRel p _ D G L R _ _ gb h hI
  obtain ⟨f, u, c, k, hsys, hm, hk, hf⟩ := hSys p D G L h hI
  obtain ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ := hsys
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left p |>.mp hkp) (Fact.out : Nat.Prime p).one_lt.ne'
    · exact hpos
  refine ⟨k, hkp, fun N => hAdm p D G L h k N hI hk0 hk, ?_⟩
  intro N S _ s o'
  have hρ : gb.ρ = (RingHom.id R) (GenCmp.baseOf gb).ρ := rfl
  have ht : ∀ i, gb.t i = (RingHom.id R).comp ((GenCmp.baseOf gb).t i) := fun i => rfl
  let o1 := GenCmp.toObj hρ ht o' (GenCmp.genericObject_kernelCondition o')
  obtain ⟨o2, ψ, hψm, hψa, hψe, hgal, ⟨hlb⟩, -⟩ :=
    GlobalTheory.T.exists_hecke_translate_locallyNoetherian_base p D R (GenCmp.baseOf gb) f u c k N N.2.1 N.2.2 hc hkp hck hlin hcomp hEF hsurj S _ o1
  let o3 := GenCmp.rebase (t := s) hρ ht rfl o2
  let o : GObj gb N s := GenCmp.toGObj o3 (GenCmp.geomFull N.2.2 o3)
  refine ⟨o, ψ, ?_⟩
  unfold UpperTheory.Gal.Int.Geo.IsTrans
  haveI := hψm
  haveI : Epi (Over.Hom.left ψ) := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
  haveI : Epi ψ := Over.epi_of_epi_left ψ
  obtain ⟨ψ', hψ'm, hψψ'⟩ := GlobalTheory.HomDescent.exists_desc S o1.A o2.A o1.A
    (HeckeAd.heckeSubA o1 (f (↑N * k)) ↑N) ψ hψm hgal (o1.act.act (k : D.O)) (o1.act.hom _)
    (fun g hg => by
      rw [oActN_act_natCast_eq_one_pow, comp_pow, Category.comp_id, HeckeAd.pow_eq_one_of_mem o1 _ g hg])
  refine ⟨hψm, hψa, ⟨ψ', k, hψ'm, ?_, ?_, ?_, hkp⟩, ?_, ?_⟩
  · intro a
    change o2.act.act a ≫ ψ' = ψ' ≫ o1.act.act a
    apply (cancel_epi ψ).1
    rw [← Category.assoc, ← hψa a, Category.assoc, hψψ', ← Category.assoc, hψψ',
      ← o1.act.mul, ← o1.act.mul, Nat.cast_comm]
  · change ψ ≫ ψ' = 𝟙 o1.A ^ k
    rw [hψψ', oActN_act_natCast_eq_one_pow]
  · change ψ' ≫ ψ = 𝟙 o2.A ^ k
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψψ', oActN_act_natCast_eq_one_pow, pow_comp, comp_pow, Category.id_comp,
      Category.comp_id]
  · obtain ⟨t, t', ht1, ht2, ht3, ht4⟩ := hm
    exact ⟨k ^ 2 / c, Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (Nat.Coprime.pow_left 2 hkp),
      ⟨hlb⟩, t, t', ht1, ht2, ht3, ht4⟩
  · intro kk _ _ t β htβ
    obtain ⟨I', hI'⟩ := o'.geom kk t β htβ
    obtain ⟨J0, hJ0e, hJ0r⟩ := HeckeAd.TateTranslAt.exists_tateIsoO_of_given D (GenCmp.baseOf gb) f u c k
      N hc hkp N.2.1 N.2.2 hck hlin hcomp hEF hsurj o1 o2.A o2.act ψ o2.ab hψm hgal hψa o2.P o2.isLB hlb
      kk t β (GenCmp.tateRestrict I') (fun y => hI' y)
    obtain ⟨I'', hI''⟩ := hFull p D R gb S s N o kk t J0
    have hNpos : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    refine ⟨I', I'', hI', fun y => ?_, ?_⟩
    · rw [hI'' _ hNpos N.2.2, ← hJ0e y]
      change toUnit (Over.mk t) ≫ o2.eta y = _
      rw [hψe y]
    · exact hRel p D G L R gb S s N (↑N * k) o' o kk t I' I'' ψ h f u c k hψm hI
        ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ hf
        (fun n hn hnp x => by rw [hI'' n hn hnp]; exact hJ0r n hn hnp x)
