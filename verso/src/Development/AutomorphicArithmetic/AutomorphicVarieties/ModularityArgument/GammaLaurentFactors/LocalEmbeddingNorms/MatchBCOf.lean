import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.MatchIndOf

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

open private normV_absNorm absNorm_pow exists_over finite_above pick pick_spec sat_unique sat_card bound_cx unr_cancel
  cnt_congr cnt_zero cnt_zero_of_unr exists_bad unrAt_iff from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.MatchIndOf

namespace UpperTheory.V.Z.Gam

namespace BaseChangeTwists

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/- English proof (translation)
The claim follows from `MonoidHom.pow_apply η.1 j _`.
-/
private theorem loc_pow (η : HChar K) (j : ℕ) (u : HeightOneSpectrum (𝓞 K)) (x : (u.adicCompletion K)ˣ) :
    (η ^ j).loc u x = η.loc u x ^ j := MonoidHom.pow_apply η.1 j _

/- English proof (translation)
Introduce `x hx` and use `by rw [loc_pow, h x hx, one_pow]`.
-/
private theorem unrAt_pow {η : HChar K} {u : HeightOneSpectrum (𝓞 K)} (h : η.UnrAt u) (j : ℕ) : (η ^ j).UnrAt u :=
  fun x hx => by rw [loc_pow, h x hx, one_pow]

/- English proof (translation)
The claim follows from `loc_pow η j u _`.
-/
private theorem val_pow (η : HChar K) (j : ℕ) (u : HeightOneSpectrum (𝓞 K)) : (η ^ j).val u = η.val u ^ j :=
  loc_pow η j u _

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext w.2.over.symm`.
-/
private theorem under_eq {v : HeightOneSpectrum (𝓞 K)} (w : PlacesOver L v) : w.1.under (𝓞 K) = v :=
  HeightOneSpectrum.ext w.2.over.symm

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hOps.1 q`. Consider the case `succ m ih`. Simplify using `only [Finset.prod_range_succ]`. Conclude with `hOps.2.1 _ _ _ _ _ _ _ _ _ (ih fun j hj => h j (by omega)) (h m (by omega))`.
-/
private theorem pair_prod (hOps : PairGOps) (q : ℝ) (A A' : ℕ → ℂ → ℂ) (β P : ℕ → ℂ[X]) (m : ℕ)
    (h : ∀ j < m, PairG (A j) (A' j) (β j) q (P j)) :
    PairG (∏ j ∈ Finset.range m, A j) (∏ j ∈ Finset.range m, A' j) (∏ j ∈ Finset.range m, β j) q
      (∏ j ∈ Finset.range m, P j) := by
  induction m with
  | zero => simpa using hOps.1 q
  | succ m ih =>
    simp only [Finset.prod_range_succ]
    exact hOps.2.1 _ _ _ _ _ _ _ _ _ (ih fun j hj => h j (by omega)) (h m (by omega))

private def Key (sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop) (satL : HeightOneSpectrum (𝓞 L) → Multiset ℂˣ → Prop)
    (u : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ w : PlacesOver L u, ∃ B, sat u B ∧ satL w.1 (B.map (· ^ fdeg w))

/- English proof (translation)
Establish `hF` using `(Filter.eventually_cofinite.1 h).image fun w => w.under (𝓞 K)`. Use `⟨hF.toFinset, fun u hu w => ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[Set.Finite.mem_toFinset]`. Take `⟨w, hw⟩` from `w`. Take `rfl : w.under (𝓞 K) = u` from `under_eq ⟨w, hw⟩`.

Establish `hgood` using `not_not.1 fun h => hu ⟨w, h, rfl⟩`. Use `hgood _ ?_` and prove the remaining obligations. Rewrite using `[normV_absNorm, normV_absNorm]`. Conclude with `absNorm_pow w`.
-/
private theorem exists_key (sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop)
    (satL : HeightOneSpectrum (𝓞 L) → Multiset ℂˣ → Prop) (h : WeakBC sat satL) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ u ∉ S, Key sat satL u := by
  have hF := (Filter.eventually_cofinite.1 h).image fun w => w.under (𝓞 K)
  refine ⟨hF.toFinset, fun u hu w => ?_⟩
  rw [Set.Finite.mem_toFinset] at hu
  obtain ⟨w, hw⟩ := w
  obtain rfl : w.under (𝓞 K) = u := under_eq ⟨w, hw⟩
  have hgood := not_not.1 fun h => hu ⟨w, h, rfl⟩
  refine hgood _ ?_
  rw [normV_absNorm, normV_absNorm]
  exact absNorm_pow w

/- English proof (translation)
Take `⟨w, rfl⟩` from `exists_over (M := L) u`. Take `⟨B, hB, -⟩` from `h ⟨w, ⟨rfl⟩⟩`. Conclude with `⟨B, hB⟩`.
-/
private theorem Key.sat {sat : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ → Prop}
    {satL : HeightOneSpectrum (𝓞 L) → Multiset ℂˣ → Prop} {u : HeightOneSpectrum (𝓞 K)} (h : Key sat satL u) :
    ∃ B, sat u B := by
  obtain ⟨w, rfl⟩ := exists_over (M := L) u
  obtain ⟨B, hB, -⟩ := h ⟨w, ⟨rfl⟩⟩
  exact ⟨B, hB⟩

/- English proof (translation)
Simplify using `only [← CG.twist_mk]`. Introduce `w`. Take `⟨B, hB, hP⟩` from `h w`. Use `⟨_, hB.twist hu, ?_⟩` and prove the remaining obligations. Establish `h` using `hP.twist (hξ w).1`.

Rewrite `h` using `[(hξ w).2, Multiset.map_map]`. Rewrite using `[Multiset.map_map]`. Use `h using 2` and compare the differences between its conclusion and the goal. Simplify using `[mul_pow]`.
-/
private theorem key_twist [IsTotallyComplex K] [IsTotallyComplex L] {n : ℕ} {π : CuspSub K n} {P : CuspSub L n}
    (χ : HChar K) (ξ : HChar L) {u : HeightOneSpectrum (𝓞 K)}
    (hξ : ∀ w : PlacesOver L u, ξ.UnrAt w.1 ∧ ξ.val w.1 = χ.val u ^ fdeg w)
    (hu : χ.UnrAt u) (h : Key (CG.mk π).HasSat (CG.mk P).HasSat u) :
    Key (CG.mk (π.twist χ)).HasSat (CG.mk (P.twist ξ)).HasSat u := by
  simp only [← CG.twist_mk]
  intro w
  obtain ⟨B, hB, hP⟩ := h w
  refine ⟨_, hB.twist hu, ?_⟩
  have h := hP.twist (hξ w).1
  rw [(hξ w).2, Multiset.map_map] at h
  rw [Multiset.map_map]
  convert h using 2
  simp [mul_pow]

/- English proof (translation)
Take `⟨c₀, hc₀⟩` from `satBd K n π`. Establish `hfin` using `finite_above (M := L) (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet`. Take `⟨SL, memSL⟩ : ∃ SL : Finset (HeightOneSpectrum (𝓞 L)), ∀ w, w ∈ SL ↔ w.under (𝓞 K) ∈ S` from `⟨hfin.toFinset, fun w => by rw [Set.Finite.mem_toFinset]; rfl⟩`. Take `⟨BK, satK⟩ : ∃ BK : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ, ∀ p ∉ S, (CG.mk π).HasSat p (BK p)` from `⟨pick (CG.mk π).HasSat, fun p hp => pick_spec (hkey p hp).sat.choose_spec⟩`. Take `⟨BL, satL⟩ : ∃ BL : HeightOneSpectrum (𝓞 L) → Multiset ℂˣ, ∀ w ∉ SL, (CG.mk P).HasSat w (BL w)` from `⟨pick (CG.mk P).HasSat, fun w hw => pick_spec (hkey _ (fun h => hw ((memSL w).2 h)) ⟨w, ⟨rfl⟩⟩).choose_spec.2⟩`.

Establish `hq : 1 < Ideal.absNorm v.asIdeal` using `NumberField.HeightOneSpectrum.one_lt_absNorm v`. Establish `side : ∀ j, ∃ β Q : ℂ[X], j < d → β ≠ 0 ∧ Q.eval 0 = 1 ∧ Q.natDegree = cnt (sK v) ((η ^ j).loc v) ∧ PairG (eulerL K (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) S) (eulerLd K (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) S) β (Ideal.absNorm v.asIdeal : ℕ) Q`. Introduce `j`. Distinguish the cases in `hj : j < d`. Use `swap`.

Conclude with `⟨0, 0, fun h => absurd h hj⟩`. Use `choose t ht using fun u => (hSupp K n (by omega) π u).2.2.2.2 (η ^ j) _ (hsK u)`. Establish `et : ∀ u, cnt (t u) 1 = cnt (sK u) ((η ^ j).loc u)` using `fun u => by rw [(ht u).2.1, mul_one]`. Take `⟨β, Q, hβ, hQ0, hQd, p⟩` from `hSide K n hn (π.twist (η ^ j)) S hK (fun p => (BK p).map (· * (η ^ j).val p)) (fun p hp => by`. Rewrite using `[← CG.twist_mk]`.

Conclude with `(satK p hp).twist (unrAt_pow (hη p hp).1 j)) t _ (fun _ => 1) hq`. Use `fun u hu => ⟨(ht u).1, fun h => by`. Rewrite using `[pow_one, not_not.1 fun e => h ((et u).trans (zK u hu e j hj))]⟩`. Use `⟨β, Q, fun _ => ⟨hβ, hQ0, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hQd, Finset.sum_eq_single_of_mem v hv (fun u hu hne => by rw [et, zK u hu hne j hj, mul_zero]), one_mul, et]`.

Establish `e : cx (fun p => (BK p).map (· * (η ^ j).val p)) = fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)`. Use function extensionality and compare the values at `p`. Simplify using `[cx, val_pow, Multiset.map_map]`. Rewrite `p` using `[e]`. Then use the resulting hypothesis. Use `choose β Q hside using side`.

Establish `pK` using `pair_prod hOps _ _ _ β Q d fun j hj => (hside j hj).2.2.2`. Take `⟨β', Q', hβ', hQ0', hQd', pL⟩` from `hSide L n hn P SL (fun w hw => (memSL w).2 (hL w hw)) BL satL sL _ (fun w => v.asIdeal.inertiaDeg' w.asIdeal) hq fun w hw => ⟨hsL w, fun h => by`. Establish `e : w.under (𝓞 K) = v` using `not_not.1 fun e => h (zL w ((memSL w).1 hw) e)`. Rewrite using `[← e]`. Conclude with `absNorm_pow w⟩`.

Take `⟨c, hc⟩` from `hReg K L d (S : Set (HeightOneSpectrum (𝓞 K))) (SL : Set (HeightOneSpectrum (𝓞 L))) (cx BK) (cx BL) (fun p => ((η.val p : ℂˣ) : ℂ)) c₀ n hd (fun w => by simpa using memSL w) (fun p hp => by`. Establish `hp' : p ∉ S` using `by simpa using hp`. Establish `hs` using `satK p hp'`. Use `⟨by simp [cx, sat_card π hs], bound_cx p le_rfl (hc₀ p _ hs), fun w => ⟨?_, ((hη p hp').2 w).2, ?_⟩⟩` and prove the remaining obligations. Conclude with `IsPrimitiveRoot.coe_units_iff.2 ((hη p hp').2 w).1`.

Take `⟨B, h1, h2⟩` from `hkey p hp' w`. Establish `s2` using `satL w.1 fun h => hp' (under_eq w ▸ (memSL w.1).1 h)`. Rewrite using `[cx, cx, sat_unique P s2 h2, sat_unique π hs h1, Multiset.map_map, Multiset.map_map]`. Conclude with `Multiset.map_congr rfl fun b _ => by simp)`. Establish `pK'` using `hOps.2.2.1 _ _ _ _ _ _ _ c pK (fun s hs => (Finset.prod_apply ..).trans ((hc s).1 hs)) (fun s hs => (Finset.prod_apply ..).trans ((hc s).2 hs))`.

Establish `e` using `hCross _ _ _ _ _ _ _ (by exact_mod_cast hq) (Finset.prod_ne_zero_iff.2 fun j hj => (hside j (Finset.mem_range.1 hj)).1) hβ' (by rw [eval_prod]; exact Finset.prod_eq_one fun j hj => (hside j (Finset.mem_range.1 hj)).2.1) hQ0' pK' pL`. Rewrite `hQd'` using `[← e, natDegree_prod _ _ (fun j hj h0 => by simpa [h0] using (hside j (Finset.mem_range.1 hj)).2.1), Finset.sum_congr rfl fun j hj => (hside j (Finset.mem_range.1 hj)).2.2.1]`. Rewrite using `[hQd']`. Establish `hsub : (Finset.univ : Finset (PlacesOver L v)).map (Function.Embedding.subtype _) ⊆ SL`. Introduce `w hw`.

Take `⟨w, -, rfl⟩` from `Finset.mem_map.1 hw`. Conclude with `(memSL w.1).2 (by rw [under_eq w]; exact hv)`. Rewrite using `[← Finset.sum_subset hsub (fun w hw hw' => ?_), Finset.sum_map]`. Both sides reduce to the same expression. Rewrite using `[zL w ((memSL w).1 hw) fun e => hw' ?_, mul_zero]`.

Conclude with `Finset.mem_map.2 ⟨⟨w, ⟨congrArg HeightOneSpectrum.asIdeal e.symm⟩⟩, Finset.mem_univ _, rfl⟩`.
-/
private theorem core [IsTotallyComplex K] [IsTotallyComplex L] (hOps : PairGOps) (hCross : CrossG) (hSide : SideG)
    (hSupp : SuppFacts) (hReg : RegroupBC) {d : ℕ} (hd : d.Prime) {n : ℕ} (hn : 2 ≤ n) (π : CuspSub K n) (P : CuspSub L n)
    (η : HChar K) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hkey : ∀ u ∉ S, Key (CG.mk π).HasSat (CG.mk P).HasSat u)
    (hη : ∀ u ∉ S, η.UnrAt u ∧ ∀ w : PlacesOver L u,
      IsPrimitiveRoot (η.val u) (fdeg w) ∧ Fintype.card (PlacesOver L u) * fdeg w = d)
    (hK : GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ⊆ S)
    (hL : ∀ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces L, w.under (𝓞 K) ∈ S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S)
    (sK : ∀ u : HeightOneSpectrum (𝓞 K), Multiset (IrrGL (u.adicCompletion K)))
    (sL : ∀ w : HeightOneSpectrum (𝓞 L), Multiset (IrrGL (w.adicCompletion L)))
    (hsK : ∀ u, SuppAt π u (sK u)) (hsL : ∀ w, SuppAt P w (sL w))
    (zK : ∀ u ∈ S, u ≠ v → ∀ j < d, cnt (sK u) ((η ^ j).loc u) = 0)
    (zL : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ S → w.under (𝓞 K) ≠ v → cnt (sL w) 1 = 0) :
    ∑ j ∈ Finset.range d, cnt (sK v) ((η ^ j).loc v) = ∑ w : PlacesOver L v, fdeg w * cnt (sL w.1) 1 := by
  obtain ⟨c₀, hc₀⟩ := satBd K n π
  have hfin := finite_above (M := L) (S : Set (HeightOneSpectrum (𝓞 K))) S.finite_toSet
  obtain ⟨SL, memSL⟩ : ∃ SL : Finset (HeightOneSpectrum (𝓞 L)), ∀ w, w ∈ SL ↔ w.under (𝓞 K) ∈ S :=
    ⟨hfin.toFinset, fun w => by rw [Set.Finite.mem_toFinset]; rfl⟩
  obtain ⟨BK, satK⟩ : ∃ BK : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ, ∀ p ∉ S, (CG.mk π).HasSat p (BK p) :=
    ⟨pick (CG.mk π).HasSat, fun p hp => pick_spec (hkey p hp).sat.choose_spec⟩
  obtain ⟨BL, satL⟩ : ∃ BL : HeightOneSpectrum (𝓞 L) → Multiset ℂˣ, ∀ w ∉ SL, (CG.mk P).HasSat w (BL w) :=
    ⟨pick (CG.mk P).HasSat, fun w hw =>
      pick_spec (hkey _ (fun h => hw ((memSL w).2 h)) ⟨w, ⟨rfl⟩⟩).choose_spec.2⟩
  have hq : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have side : ∀ j, ∃ β Q : ℂ[X], j < d → β ≠ 0 ∧ Q.eval 0 = 1 ∧ Q.natDegree = cnt (sK v) ((η ^ j).loc v) ∧
      PairG (eulerL K (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) S)
        (eulerLd K (fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j)) S) β (Ideal.absNorm v.asIdeal : ℕ) Q := by
    intro j
    by_cases hj : j < d
    swap
    · exact ⟨0, 0, fun h => absurd h hj⟩
    choose t ht using fun u => (hSupp K n (by omega) π u).2.2.2.2 (η ^ j) _ (hsK u)
    have et : ∀ u, cnt (t u) 1 = cnt (sK u) ((η ^ j).loc u) := fun u => by rw [(ht u).2.1, mul_one]
    obtain ⟨β, Q, hβ, hQ0, hQd, p⟩ := hSide K n hn (π.twist (η ^ j)) S hK (fun p => (BK p).map (· * (η ^ j).val p))
      (fun p hp => by
        rw [← CG.twist_mk]
        exact (satK p hp).twist (unrAt_pow (hη p hp).1 j)) t _ (fun _ => 1) hq
      fun u hu => ⟨(ht u).1, fun h => by
        rw [pow_one, not_not.1 fun e => h ((et u).trans (zK u hu e j hj))]⟩
    refine ⟨β, Q, fun _ => ⟨hβ, hQ0, ?_, ?_⟩⟩
    · rw [hQd, Finset.sum_eq_single_of_mem v hv (fun u hu hne => by rw [et, zK u hu hne j hj, mul_zero]), one_mul, et]
    · have e : cx (fun p => (BK p).map (· * (η ^ j).val p)) =
          fun p => (cx BK p).map (· * ((η.val p : ℂˣ) : ℂ) ^ j) := by
        funext p
        simp [cx, val_pow, Multiset.map_map]
      rwa [e] at p
  choose β Q hside using side
  have pK := pair_prod hOps _ _ _ β Q d fun j hj => (hside j hj).2.2.2
  obtain ⟨β', Q', hβ', hQ0', hQd', pL⟩ := hSide L n hn P SL (fun w hw => (memSL w).2 (hL w hw)) BL satL sL _
    (fun w => v.asIdeal.inertiaDeg' w.asIdeal) hq fun w hw => ⟨hsL w, fun h => by
      have e : w.under (𝓞 K) = v := not_not.1 fun e => h (zL w ((memSL w).1 hw) e)
      rw [← e]
      exact absNorm_pow w⟩
  obtain ⟨c, hc⟩ := hReg K L d (S : Set (HeightOneSpectrum (𝓞 K))) (SL : Set (HeightOneSpectrum (𝓞 L))) (cx BK) (cx BL)
    (fun p => ((η.val p : ℂˣ) : ℂ)) c₀ n hd (fun w => by simpa using memSL w)
    (fun p hp => by
      have hp' : p ∉ S := by simpa using hp
      have hs := satK p hp'
      refine ⟨by simp [cx, sat_card π hs], bound_cx p le_rfl (hc₀ p _ hs), fun w => ⟨?_, ((hη p hp').2 w).2, ?_⟩⟩
      · exact IsPrimitiveRoot.coe_units_iff.2 ((hη p hp').2 w).1
      · obtain ⟨B, h1, h2⟩ := hkey p hp' w
        have s2 := satL w.1 fun h => hp' (under_eq w ▸ (memSL w.1).1 h)
        rw [cx, cx, sat_unique P s2 h2, sat_unique π hs h1, Multiset.map_map, Multiset.map_map]
        exact Multiset.map_congr rfl fun b _ => by simp)
  have pK' := hOps.2.2.1 _ _ _ _ _ _ _ c pK (fun s hs => (Finset.prod_apply ..).trans ((hc s).1 hs))
    (fun s hs => (Finset.prod_apply ..).trans ((hc s).2 hs))
  have e := hCross _ _ _ _ _ _ _ (by exact_mod_cast hq)
    (Finset.prod_ne_zero_iff.2 fun j hj => (hside j (Finset.mem_range.1 hj)).1) hβ'
    (by rw [eval_prod]; exact Finset.prod_eq_one fun j hj => (hside j (Finset.mem_range.1 hj)).2.1) hQ0' pK' pL
  rw [← e, natDegree_prod _ _ (fun j hj h0 => by simpa [h0] using (hside j (Finset.mem_range.1 hj)).2.1),
    Finset.sum_congr rfl fun j hj => (hside j (Finset.mem_range.1 hj)).2.2.1] at hQd'
  rw [hQd']
  have hsub : (Finset.univ : Finset (PlacesOver L v)).map (Function.Embedding.subtype _) ⊆ SL := by
    intro w hw
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hw
    exact (memSL w.1).2 (by rw [under_eq w]; exact hv)
  rw [← Finset.sum_subset hsub (fun w hw hw' => ?_), Finset.sum_map]
  · rfl
  · rw [zL w ((memSL w).1 hw) fun e => hw' ?_, mul_zero]
    exact Finset.mem_map.2 ⟨⟨w, ⟨congrArg HeightOneSpectrum.asIdeal e.symm⟩⟩, Finset.mem_univ _, rfl⟩

/- English proof (translation)
Take `⟨η, h1, h3⟩` from `normCnt K L hd`. Use `⟨⟨(Filter.eventually_cofinite.1 h1).toFinset, fun u hu w θ hθ hn => ?_⟩, fun u w θ hθ => ((h3 u w).2.2 θ (isSmoothChar_of_isUnram hθ)).2.1 hθ⟩` and prove the remaining obligations. Rewrite `hu` using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not]`. Establish `hc` using `((h3 u w).2.2 θ hθ).2.2 hn`. Establish `hpos : 0 < ∑ w' : PlacesOver L u, fdeg w'`.

Establish `hw` using `(hu.2 w).2`. Establish `: 0 < fdeg w` using `Nat.pos_of_ne_zero fun e => by`. Rewrite `hw` using `[e, mul_zero]`. Conclude with `hd.ne_zero hw.symm`. Conclude with `lt_of_lt_of_le this (Finset.single_le_sum (f := fun w' : PlacesOver L u => fdeg w') (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))`.

Rewrite `hpos` using `[← hc]`. Take `⟨j, hj⟩` from `Finset.card_pos.1 hpos`. Conclude with `unr_cancel ((unrAt_iff _ u).1 (unrAt_pow hu.1 j)) (mul_comm θ _ ▸ (Finset.mem_filter.1 hj).2)`.
-/
private theorem norm_units [IsGalois K L] (hd : (Module.finrank K L).Prime) :
    (∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ u ∉ T, ∀ (w : PlacesOver L u) (θ : (u.adicCompletion K)ˣ →* ℂˣ),
      IsSmoothChar θ → IsUnram (θ.comp (nm w)) → IsUnram θ) ∧
    ∀ (u : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L u) (θ : (u.adicCompletion K)ˣ →* ℂˣ), IsUnram θ →
      IsUnram (θ.comp (nm w)) := by
  obtain ⟨η, h1, h3⟩ := normCnt K L hd
  refine ⟨⟨(Filter.eventually_cofinite.1 h1).toFinset, fun u hu w θ hθ hn => ?_⟩,
    fun u w θ hθ => ((h3 u w).2.2 θ (isSmoothChar_of_isUnram hθ)).2.1 hθ⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hu
  have hc := ((h3 u w).2.2 θ hθ).2.2 hn
  have hpos : 0 < ∑ w' : PlacesOver L u, fdeg w' := by
    have hw := (hu.2 w).2
    have : 0 < fdeg w := Nat.pos_of_ne_zero fun e => by
      rw [e, mul_zero] at hw
      exact hd.ne_zero hw.symm
    exact lt_of_lt_of_le this (Finset.single_le_sum (f := fun w' : PlacesOver L u => fdeg w')
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ w))
  rw [← hc] at hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
  exact unr_cancel ((unrAt_iff _ u).1 (unrAt_pow hu.1 j)) (mul_comm θ _ ▸ (Finset.mem_filter.1 hj).2)

end BaseChangeTwists

open BaseChangeTwists in
/- English proof (translation)
Introduce `hOps hCross hSide hSupp hNL hTw hReg K L _ _ _ _ _ _ _ _ hd n hn π P hW η hη v s s' hs hs' θ hθ`. Take `⟨S₁, hkey⟩` from `exists_key _ _ hW`. Take `⟨⟨T, hT⟩, hnm⟩` from `norm_units hd`. Take `⟨R, hR⟩ : ∃ R : Finset (HeightOneSpectrum (𝓞 K)), ∀ u ∉ R, η.UnrAt u ∧ ∀ w : PlacesOver L u, IsPrimitiveRoot (η.val u) (fdeg w) ∧ Fintype.card (PlacesOver L u) * fdeg w = Module.finrank K L` from `⟨(Filter.eventually_cofinite.1 hη).toFinset, fun u hu => by`. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hu⟩` and apply the resulting hypothesis.

Establish `FK` using `hSupp K n (by omega) π`. Establish `FL` using `hSupp L n (by omega) P`. Use `choose sK hsK using fun u => (FK u).1`. Use `choose sL hsL using fun w => (FL w).1`. Use `choose bK hbK using fun u => exists_bad (sK u)`.

Use `choose bL hbL using fun w => exists_bad (sL w)`. Take `⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S₀ ↔ u = v ∨ u ∈ S₁ ∨ u ∈ T ∨ u ∈ R ∨ u ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∨ ∃ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces L, w.under (𝓞 K) = u` from `⟨insert v (S₁ ∪ (T ∪ (R ∪ (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∪ (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces L).image fun w => w.under (𝓞 K))))), fun u => by simp⟩`. Take `⟨χ, hχv, hχ⟩` from `hTw K L v θ hθ S₀ (fun u => (bK u ×ˢ Finset.range (Module.finrank K L)).image fun x => x.1 * (η ^ x.2).loc u) bL`. Take `⟨ξ, hξ⟩` from `hNL K L χ`. Take `⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S ↔ u ∈ S₀ ∨ ¬ χ.UnrAt u` from `⟨S₀ ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset, fun u => by simp⟩`.

Use `choose tK htK using fun u => (FK u).2.2.2.2 χ _ (hsK u)`. Use `choose tL htL using fun w => (FL w).2.2.2.2 ξ _ (hsL w)`. Establish `k₀ : ∀ u ∉ S₀, Key (CG.mk π).HasSat (CG.mk P).HasSat u` using `fun u hu => hkey u fun h => hu ((hS₀ _).2 (Or.inr (Or.inl h)))`. Establish `r₀ : ∀ u ∉ S₀, u ∉ R` using `fun u hu h => hu ((hS₀ _).2 (by tauto))`. Establish `main` using `core hOps hCross hSide hSupp hReg hd hn (π.twist χ) (P.twist ξ) η S (fun u hu => by`.

Establish `hur : χ.UnrAt u` using `not_not.1 fun h => hu ((hS _).2 (Or.inr h))`. Conclude with `key_twist χ ξ (fun w => (hξ u w).2.1 hur) hur (k₀ u fun h => hu ((hS _).2 (Or.inl h))))`. Use the proof step `(fun u hu => hR u (r₀ u fun h => hu ((hS _).2 (Or.inl h))))`. Use the proof step `(fun u hu => (hS _).2 (Or.inl ((hS₀ _).2 (by tauto))))`. Use the proof step `(fun w hw => (hS _).2 (Or.inl ((hS₀ _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩))))))))`.

Use `v ((hS _).2 (Or.inl ((hS₀ _).2 (Or.inl rfl)))) tK tL (fun u => (htK u).1) (fun w => (htL w).1)`. Use the proof step `(fun u hu hne j hj => by`. Rewrite using `[(htK u).2.1]`. Distinguish the cases in `h0 : u ∈ S₀`. Use `cnt_zero _ _ fun ζ hζ hy => ?_` and prove the remaining obligations.

Rewrite using `[mul_comm (χ.loc u), ← mul_assoc]`. Conclude with `(hχ u h0 hne).1 _ (Finset.mem_image.2 ⟨(ζ, j), Finset.mem_product.2 ⟨hbK u ζ hζ hy, Finset.mem_range.2 hj⟩, rfl⟩)`. Take `⟨B, hB⟩` from `(k₀ u h0).sat`. Use `cnt_zero_of_unr _ _ ((FK _).2.2.2.1 _ B (hsK _) hB) fun h => ((hS _).1 hu).resolve_left h0 ((unrAt_iff χ _).2 ?_)` and prove the remaining obligations. Rewrite `h` using `[mul_comm]`.

Conclude with `unr_cancel ((unrAt_iff _ u).1 (unrAt_pow (hR u (r₀ u h0)).1 j)) h)`. Use the proof step `(fun w hu hne => by`. Rewrite using `[(htL w).2.1, mul_one, (hξ (w.under (𝓞 K)) ⟨w, ⟨rfl⟩⟩).1]`. Distinguish the cases in `h0 : w.under (𝓞 K) ∈ S₀`. Conclude with `cnt_zero _ _ fun ζ hζ hy => (hχ _ h0 hne).2 ⟨w, ⟨rfl⟩⟩ ζ (hbL w ζ hζ hy)`.

Take `⟨B, -, hB⟩` from `k₀ _ h0 ⟨w, ⟨rfl⟩⟩`. Conclude with `cnt_zero_of_unr _ _ ((FL _).2.2.2.1 _ _ (hsL _) hB) fun h => ((hS _).1 hu).resolve_left h0 ((unrAt_iff χ _).2 (hT _ (fun h' => h0 ((hS₀ _).2 (by tauto))) _ _ (GlobalTheory.HeckeComp.smooth_loc χ _) h)))`. Use `Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (main.trans (Finset.sum_congr rfl fun w _ => ?_))` and prove the remaining obligations. Rewrite using `[(htK v).2.1, (FK v).2.1 _ _ (hsK v) hs]`. Use `(cnt_congr _ ?_).symm` and prove the remaining obligations.

Rewrite using `[mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]` and apply the resulting hypothesis. Rewrite using `[(htL w.1).2.1, mul_one, (hξ v w).1, (FL w.1).2.1 _ _ (hsL w.1) (hs' w)]`. Use `congr 1`. Conclude with `cnt_congr _ (hnm v w _ hχv)`.
-/
theorem matchBCOf : MatchBCOf := by
  intro hOps hCross hSide hSupp hNL hTw hReg K L _ _ _ _ _ _ _ _ hd n hn π P hW η hη v s s' hs hs' θ hθ
  obtain ⟨S₁, hkey⟩ := exists_key _ _ hW
  obtain ⟨⟨T, hT⟩, hnm⟩ := norm_units hd
  obtain ⟨R, hR⟩ : ∃ R : Finset (HeightOneSpectrum (𝓞 K)), ∀ u ∉ R, η.UnrAt u ∧ ∀ w : PlacesOver L u,
      IsPrimitiveRoot (η.val u) (fdeg w) ∧ Fintype.card (PlacesOver L u) * fdeg w = Module.finrank K L :=
    ⟨(Filter.eventually_cofinite.1 hη).toFinset, fun u hu => by
      rwa [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hu⟩
  have FK := hSupp K n (by omega) π
  have FL := hSupp L n (by omega) P
  choose sK hsK using fun u => (FK u).1
  choose sL hsL using fun w => (FL w).1
  choose bK hbK using fun u => exists_bad (sK u)
  choose bL hbL using fun w => exists_bad (sL w)
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S₀ ↔ u = v ∨ u ∈ S₁ ∨ u ∈ T ∨ u ∈ R ∨
      u ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∨
      ∃ w ∈ GroundTheory.Automorphic.GJStandardL.ramifiedPlaces L, w.under (𝓞 K) = u :=
    ⟨insert v (S₁ ∪ (T ∪ (R ∪ (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces K ∪
      (GroundTheory.Automorphic.GJStandardL.ramifiedPlaces L).image fun w => w.under (𝓞 K))))), fun u => by simp⟩
  obtain ⟨χ, hχv, hχ⟩ := hTw K L v θ hθ S₀
    (fun u => (bK u ×ˢ Finset.range (Module.finrank K L)).image fun x => x.1 * (η ^ x.2).loc u) bL
  obtain ⟨ξ, hξ⟩ := hNL K L χ
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ u, u ∈ S ↔ u ∈ S₀ ∨ ¬ χ.UnrAt u :=
    ⟨S₀ ∪ (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset, fun u => by simp⟩
  choose tK htK using fun u => (FK u).2.2.2.2 χ _ (hsK u)
  choose tL htL using fun w => (FL w).2.2.2.2 ξ _ (hsL w)
  have k₀ : ∀ u ∉ S₀, Key (CG.mk π).HasSat (CG.mk P).HasSat u :=
    fun u hu => hkey u fun h => hu ((hS₀ _).2 (Or.inr (Or.inl h)))
  have r₀ : ∀ u ∉ S₀, u ∉ R := fun u hu h => hu ((hS₀ _).2 (by tauto))
  have main := core hOps hCross hSide hSupp hReg hd hn (π.twist χ) (P.twist ξ) η S
    (fun u hu => by
      have hur : χ.UnrAt u := not_not.1 fun h => hu ((hS _).2 (Or.inr h))
      exact key_twist χ ξ (fun w => (hξ u w).2.1 hur) hur (k₀ u fun h => hu ((hS _).2 (Or.inl h))))
    (fun u hu => hR u (r₀ u fun h => hu ((hS _).2 (Or.inl h))))
    (fun u hu => (hS _).2 (Or.inl ((hS₀ _).2 (by tauto))))
    (fun w hw => (hS _).2 (Or.inl ((hS₀ _).2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨w, hw, rfl⟩))))))))
    v ((hS _).2 (Or.inl ((hS₀ _).2 (Or.inl rfl)))) tK tL (fun u => (htK u).1) (fun w => (htL w).1)
    (fun u hu hne j hj => by
      rw [(htK u).2.1]
      by_cases h0 : u ∈ S₀
      · refine cnt_zero _ _ fun ζ hζ hy => ?_
        rw [mul_comm (χ.loc u), ← mul_assoc]
        exact (hχ u h0 hne).1 _ (Finset.mem_image.2 ⟨(ζ, j),
          Finset.mem_product.2 ⟨hbK u ζ hζ hy, Finset.mem_range.2 hj⟩, rfl⟩)
      · obtain ⟨B, hB⟩ := (k₀ u h0).sat
        refine cnt_zero_of_unr _ _ ((FK _).2.2.2.1 _ B (hsK _) hB)
          fun h => ((hS _).1 hu).resolve_left h0 ((unrAt_iff χ _).2 ?_)
        rw [mul_comm] at h
        exact unr_cancel ((unrAt_iff _ u).1 (unrAt_pow (hR u (r₀ u h0)).1 j)) h)
    (fun w hu hne => by
      rw [(htL w).2.1, mul_one, (hξ (w.under (𝓞 K)) ⟨w, ⟨rfl⟩⟩).1]
      by_cases h0 : w.under (𝓞 K) ∈ S₀
      · exact cnt_zero _ _ fun ζ hζ hy => (hχ _ h0 hne).2 ⟨w, ⟨rfl⟩⟩ ζ (hbL w ζ hζ hy)
      · obtain ⟨B, -, hB⟩ := k₀ _ h0 ⟨w, ⟨rfl⟩⟩
        exact cnt_zero_of_unr _ _ ((FL _).2.2.2.1 _ _ (hsL _) hB)
          fun h => ((hS _).1 hu).resolve_left h0 ((unrAt_iff χ _).2
            (hT _ (fun h' => h0 ((hS₀ _).2 (by tauto))) _ _ (GlobalTheory.HeckeComp.smooth_loc χ _) h)))
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) (main.trans (Finset.sum_congr rfl fun w _ => ?_))
  · rw [(htK v).2.1, (FK v).2.1 _ _ (hsK v) hs]
    refine (cnt_congr _ ?_).symm
    rwa [mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
  · rw [(htL w.1).2.1, mul_one, (hξ v w).1, (FL w.1).2.1 _ _ (hsL w.1) (hs' w)]
    congr 1
    exact cnt_congr _ (hnm v w _ hχv)

end UpperTheory.V.Z.Gam
