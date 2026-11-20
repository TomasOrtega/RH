import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DefIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ZpowWNe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ConjVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBstab
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBdim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrBrig
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCfix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrGood
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrSetlift
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LcMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.BorelProjectionIsTwoCocycle
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCocv
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ValSubOneMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrTsurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.GgMapOfGL
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TanFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrMazur

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S x L`. Use `haveI : CharP (ResidueField O) l := IsCoef.char`. Use `haveI : IsNoetherianRing L.O' := inferInstance`. Use `haveI : IsAdicComplete (maximalIdeal L.O') L.O' := IsCoef.complete`. Use `haveI : Finite (ResidueField L.O') := IsCoef.fin`.

Use `haveI : CharP (ResidueField L.O') l := IsCoef.char`. Establish `hU : NRep.Univ L.O' L.ρ`. Use `⟨(loc_rho hF hn S x L).1, ?_⟩` and prove the remaining obligations. Introduce `C _ _ _ ρ' hc hb`. Conclude with `def_iso hF hn S x L C ρ' hc hb`.

Take `⟨B, hBo, hBc⟩` from `pr_box hF L.R (maximalIdeal L.R) L.ρ (loc_rho hF hn S x L).1 (fun v => flag hF hn S L.R (L.ι : S.A →+* L.R) v)`. Take `⟨φ, hφ⟩` from `(pr_res hF hn S x L).1`. Establish `hG` using `pr_good hF hn (ResidueField L.O') φ _ hφ`. Use `haveI : Module.Finite (ResidueField L.O') (Tan L.O' L.R) := (pr_tan L.O' L.R).1`. Establish `hBo'` using `hBo.map (res L.O' L.R : L.R →+* ResidueField L.O')`.

Establish `hres` using `pr_res hF hn S x L`. Establish `hcount` using `pr_count (K := ResidueField L.O') F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b ((Box.tanCo L.O' B).comp (Tan L.O' L.R).subtype) (fun v Y hY => pr_brig (ResidueField L.O') _ (Box.bar L.O' B) hBo' hG.1 v Y hY) (fun z hz => by`. Take `⟨D, hD, X, hX⟩` from `pr_tsurj hF L.O' L.R L.ρ B hU hBo hBc hG.1 z hz`. Conclude with `⟨⟨D, hD⟩, X, hX⟩)`. Take `⟨D₀, hD₀, hD₀s⟩` from `pr_tor hF L.O' L.R L.ρ B hU hBo hBc hG.1 hG.2.2`.

Establish `h1` using `hcount.2 _ ⟨D₀, hD₀⟩ hG.2.1 hD₀s`. Establish `hec` using `hF.ec (ResidueField L.O') (Matrix (Fin n) (Fin n) (ResidueField L.O')) (Box.bar L.O' B).ad (Box.bar L.O' B).b (pr_open hF L.O' L.R B hBc).2.1 (fun v s X hX => pr_bstab _ (Box.bar L.O' B) v s X hX) (fun f hf => pr_dual hF hn (ResidueField L.O') φ _ (Box.bar L.O' B) hBo' hφ hres.2 …`. Establish `h2K : (2 : ResidueField L.O') ≠ 0`. Introduce `h`. Establish `hd` using `(CharP.cast_eq_zero_iff (ResidueField L.O') l 2).1 (by exact_mod_cast h)`.

Establish `hl` using `(Fact.out : l.Prime)`. Establish `h4` using `Nat.le_of_dvd (by norm_num) hd`. Establish `h5` using `hl.two_le`. Establish `h6` using `hF.l_odd`. Use linear arithmetic over natural numbers and integers.

Establish `hκ : ∀ w : F.Inf, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker = (n * n - n) / 2`. Introduce `w`. Establish `hsq : (Box.bar L.O' B).r (F.cw w) * (Box.bar L.O' B).r (F.cw w) = 1`. Rewrite using `[← map_mul, hF.cw_sq w, map_one]`. Establish `hr : ((Box.bar L.O' B).r (F.cw w)).right = -1`.

Rewrite using `[(Box.bar L.O' B).nu, hF.del_cw w]`. Establish `key : 2 * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker + n = n * n` using `pr_cfix (ResidueField L.O') n _ h2K hsq hr`. Establish `hle : n ≤ n * n` using `Nat.le_mul_self n`. Use linear arithmetic over natural numbers and integers. Establish `hβ : ∀ v : F.V, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = (n * n - n) / 2 + n`.

Introduce `v`. Establish `key : 2 * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = n * (n + 1)` using `pr_bdim (ResidueField L.O') n ((Box.bar L.O' B).g v)`. Establish `hle : n ≤ n * n` using `Nat.le_mul_self n`. Establish `e : n * (n + 1) = n * n + n` using `by ring`. Use linear arithmetic over natural numbers and integers.

Establish `hsum1 : ∑ v : F.V, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = F.d * ((n * n - n) / 2) + F.d * n`. Rewrite using `[Finset.sum_congr rfl (fun v _ => by rw [hβ v]), ← Finset.sum_mul]`. Use `show F.d * ((n * n - n) / 2 + n) = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hsum2 : ∑ w : F.Inf, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker = F.d * ((n * n - n) / 2)`.

Simplify using `only [hκ, Finset.sum_const, Finset.card_univ, smul_eq_mul, hF.card_inf]`. Establish `hT : Module.finrank (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) + n * F.d + 1 ≤ Module.finrank (ResidueField L.O') (Tan L.O' L.R)`. Establish `e` using `hec.2`. Rewrite `e` using `[hsum1, hsum2]`. Establish `: n * F.d = F.d * n` using `Nat.mul_comm _ _`.

Use linear arithmetic over natural numbers and integers. Establish `hobs : HasObs L.O' L.R (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b)`. Introduce `C' _ _ _ p hp hm`. Take `⟨D⟩` from `pr_setlift hF L.O' C' L.R p B hp hm hBc`. Establish `hZ : ∀ u, D.co u ∈ continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b`.

Introduce `u`. Take `⟨_, _, hlc1, hlc2⟩` from `pr_omk hF L.O' C' L.R p B D hm`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hlc1.comp (fun M => M.map (evK (RingHom.ker p) u))`. Introduce `v`.

Conclude with `(hlc2 v).comp (fun M => M.map (evK (RingHom.ker p) u))`. Introduce `s t r`. Conclude with `borelProjection_isTwoCocycle hF L.O' C' L.R p B D u hm s t r`. Introduce `v s t`. Conclude with `pr_cocv hF L.O' C' L.R p B D u hm v s t`.

Use `⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ D.co hZ), ?_⟩` and prove the remaining obligations. Introduce `u hu C'' _ _ _ q p'' hc hq hk`. Use `pr_obs hF L.O' L.R L.ρ B hU hBo hBc hG.1 C' p D u hm ?_ C'' q p'' hc hq hk` and prove the remaining obligations. Establish `h' : (⟨D.co u, hZ u⟩ : continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) ∈ Submodule.comap (continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b).subtype (continuousCoboundaries2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b)` using `(Submodule.Quotient.mk_eq_zero _).1 hu`. Conclude with `h'`.

Use `haveI : Module.Finite (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) := hec.1`. Establish `hobs' : HasObs L.O' L.R (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b × (Fin (Module.finrank (ResidueField L.O') (Tan L.O' L.R) - (n * F.d + 1) - Module.finrank (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b)) → ResidueField L.O'))`. Introduce `C' _ _ _ p hp hm`. Take `⟨ob, hob⟩` from `hobs C' p hp hm`. Use `⟨(LinearMap.inl _ _ _).comp ob, fun u hu => hob u ?_⟩` and prove the remaining obligations.

Simplify using `using hu`. Take `⟨p, f, hs, hk⟩` from `pr_mazur L.O' L.R _ hobs'`. Use `⟨_, _, p, f, ?_, hs, hk⟩` and prove the remaining obligations. Rewrite using `[Module.finrank_prod, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.Fr.pres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), L.Pres := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  haveI : CharP (ResidueField O) l := IsCoef.char
  haveI : IsNoetherianRing L.O' := inferInstance
  haveI : IsAdicComplete (maximalIdeal L.O') L.O' := IsCoef.complete
  haveI : Finite (ResidueField L.O') := IsCoef.fin
  haveI : CharP (ResidueField L.O') l := IsCoef.char
  have hU : NRep.Univ L.O' L.ρ := by
    refine ⟨(loc_rho hF hn S x L).1, ?_⟩
    intro C _ _ _ ρ' hc hb
    exact def_iso hF hn S x L C ρ' hc hb
  obtain ⟨B, hBo, hBc⟩ := pr_box hF L.R (maximalIdeal L.R) L.ρ (loc_rho hF hn S x L).1 (fun v => flag hF hn S L.R (L.ι : S.A →+* L.R) v)
  obtain ⟨φ, hφ⟩ := (pr_res hF hn S x L).1
  have hG := pr_good hF hn (ResidueField L.O') φ _ hφ
  haveI : Module.Finite (ResidueField L.O') (Tan L.O' L.R) := (pr_tan L.O' L.R).1
  have hBo' := hBo.map (res L.O' L.R : L.R →+* ResidueField L.O')
  have hres := pr_res hF hn S x L
  have hcount := pr_count (K := ResidueField L.O') F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b
    ((Box.tanCo L.O' B).comp (Tan L.O' L.R).subtype)
    (fun v Y hY => pr_brig (ResidueField L.O') _ (Box.bar L.O' B) hBo' hG.1 v Y hY)
    (fun z hz => by
      obtain ⟨D, hD, X, hX⟩ := pr_tsurj hF L.O' L.R L.ρ B hU hBo hBc hG.1 z hz
      exact ⟨⟨D, hD⟩, X, hX⟩)
  obtain ⟨D₀, hD₀, hD₀s⟩ := pr_tor hF L.O' L.R L.ρ B hU hBo hBc hG.1 hG.2.2
  have h1 := hcount.2 _ ⟨D₀, hD₀⟩ hG.2.1 hD₀s
  have hec := hF.ec (ResidueField L.O') (Matrix (Fin n) (Fin n) (ResidueField L.O')) (Box.bar L.O' B).ad (Box.bar L.O' B).b
    (pr_open hF L.O' L.R B hBc).2.1
    (fun v s X hX => pr_bstab _ (Box.bar L.O' B) v s X hX)
    (fun f hf => pr_dual hF hn (ResidueField L.O') φ _ (Box.bar L.O' B) hBo' hφ hres.2 f hf)
  have h2K : (2 : ResidueField L.O') ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff (ResidueField L.O') l 2).1 (by exact_mod_cast h)
    have hl := (Fact.out : l.Prime)
    have h4 := Nat.le_of_dvd (by norm_num) hd
    have h5 := hl.two_le
    have h6 := hF.l_odd
    omega
  have hκ : ∀ w : F.Inf, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker = (n * n - n) / 2 := by
    intro w
    have hsq : (Box.bar L.O' B).r (F.cw w) * (Box.bar L.O' B).r (F.cw w) = 1 := by
      rw [← map_mul, hF.cw_sq w, map_one]
    have hr : ((Box.bar L.O' B).r (F.cw w)).right = -1 := by
      rw [(Box.bar L.O' B).nu, hF.del_cw w]
    have key : 2 * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker + n = n * n :=
      pr_cfix (ResidueField L.O') n _ h2K hsq hr
    have hle : n ≤ n * n := Nat.le_mul_self n
    omega
  have hβ : ∀ v : F.V, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = (n * n - n) / 2 + n := by
    intro v
    have key : 2 * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = n * (n + 1) :=
      pr_bdim (ResidueField L.O') n ((Box.bar L.O' B).g v)
    have hle : n ≤ n * n := Nat.le_mul_self n
    have e : n * (n + 1) = n * n + n := by ring
    omega
  have hsum1 : ∑ v : F.V, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = F.d * ((n * n - n) / 2) + F.d * n := by
    rw [Finset.sum_congr rfl (fun v _ => by rw [hβ v]), ← Finset.sum_mul]
    show F.d * ((n * n - n) / 2 + n) = _
    ring
  have hsum2 : ∑ w : F.Inf, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker = F.d * ((n * n - n) / 2) := by
    simp only [hκ, Finset.sum_const, Finset.card_univ, smul_eq_mul, hF.card_inf]
  have hT : Module.finrank (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) + n * F.d + 1 ≤ Module.finrank (ResidueField L.O') (Tan L.O' L.R) := by
    have e := hec.2
    rw [hsum1, hsum2] at e
    have : n * F.d = F.d * n := Nat.mul_comm _ _
    omega
  have hobs : HasObs L.O' L.R (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) := by
    intro C' _ _ _ p hp hm
    obtain ⟨D⟩ := pr_setlift hF L.O' C' L.R p B hp hm hBc
    have hZ : ∀ u, D.co u ∈ continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b := by
      intro u
      obtain ⟨_, _, hlc1, hlc2⟩ := pr_omk hF L.O' C' L.R p B D hm
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hlc1.comp (fun M => M.map (evK (RingHom.ker p) u))
      · intro v
        exact (hlc2 v).comp (fun M => M.map (evK (RingHom.ker p) u))
      · intro s t r
        exact borelProjection_isTwoCocycle hF L.O' C' L.R p B D u hm s t r
      · intro v s t
        exact pr_cocv hF L.O' C' L.R p B D u hm v s t
    refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ D.co hZ), ?_⟩
    intro u hu C'' _ _ _ q p'' hc hq hk
    refine pr_obs hF L.O' L.R L.ρ B hU hBo hBc hG.1 C' p D u hm ?_ C'' q p'' hc hq hk
    have h' : (⟨D.co u, hZ u⟩ : continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) ∈
        Submodule.comap (continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b).subtype (continuousCoboundaries2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) :=
      (Submodule.Quotient.mk_eq_zero _).1 hu
    exact h'
  haveI : Module.Finite (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) := hec.1
  have hobs' : HasObs L.O' L.R (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b ×
      (Fin (Module.finrank (ResidueField L.O') (Tan L.O' L.R) - (n * F.d + 1) -
        Module.finrank (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b)) → ResidueField L.O')) := by
    intro C' _ _ _ p hp hm
    obtain ⟨ob, hob⟩ := hobs C' p hp hm
    refine ⟨(LinearMap.inl _ _ _).comp ob, fun u hu => hob u ?_⟩
    simpa using hu
  obtain ⟨p, f, hs, hk⟩ := pr_mazur L.O' L.R _ hobs'
  refine ⟨_, _, p, f, ?_, hs, hk⟩
  rw [Module.finrank_prod, Module.finrank_fin_fun]
  omega
