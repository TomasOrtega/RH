import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSumsAtHalfCurveFraction

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj

namespace GlobalTheory.FibreFrame

variable {K R R' : Type} [CommRing K] [CommRing R] [CommRing R'] {X Y Z : Scheme.{0}} {L : LB Z} {m : ℕ}

/- English proof (translation)
Introduce `_ hz` and use `Set.mem_iInter.2 fun _ => h hz`.
-/
theorem le_wchart {π : X ⟶ Z} {q : Sp R ⟶ X} {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

/- English proof (translation)
The claim follows from `HolHom.valR_spMap ρ q _ (le_wchart h) _`.
-/
theorem sval_spMap {π : X ⟶ Z} (s : SecP L π m) (ρ : R →+* R') (q : Sp R ⟶ X) {j : L.ι}
    (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) : ArcPts.sval s (spMap ρ ≫ q) j = ρ (ArcPts.sval s q j) :=
  HolHom.valR_spMap ρ q _ (le_wchart h) _

/- English proof (translation)
Substitute `e` using the available equality. Use `⟨DVR.pullSec L (fun _ : Fin 1 => π) (fun _ => (m : ℤ)) s h, fun _ _ => rfl, fun R _ q j hj => ?_⟩` and prove the remaining obligations. Conclude with `(HolHom.valR_res q _ _ (le_wchart hj)).trans (HolHom.valR_comp q h _ _).symm`.
-/
theorem exists_pull {π : X ⟶ Z} (s : SecP L π m) (h : Y ⟶ X) {π' : Y ⟶ Z} (e : h ≫ π = π') :
    ∃ s' : SecP L π' m, (∀ j (le : LB.wchart L (fun _ : Fin 1 => π') j ≤ h ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => π) j),
        s'.f j = (Y.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
        ArcPts.sval s' q j = ArcPts.sval s (q ≫ h) j := by
  subst e
  refine ⟨DVR.pullSec L (fun _ : Fin 1 => π) (fun _ => (m : ℤ)) s h, fun _ _ => rfl, fun R _ q j hj => ?_⟩
  exact (HolHom.valR_res q _ _ (le_wchart hj)).trans (HolHom.valR_comp q h _ _).symm

/- English proof (translation)
The claim follows from `congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)`.
-/
theorem res_constFn (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    (X.presheaf.map (homOfLE h).op).hom (constFn p U a) = constFn p V a :=
  congrArg (fun q : Γ(Sp K, ⊤) ⟶ Γ(X, V) => q.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (p.appLE_map (U := ⊤) (V := U) le_top (homOfLE h).op)

/- English proof (translation)
Use `(HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_` and prove the remaining obligations. Rewrite using `[hq, Conv.valR_spMap_top]`.
-/
theorem valR_constFn (p : X ⟶ Sp K) (f : K →+* R) (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ q ⁻¹ᵁ U) (a : K) : valR q U (constFn p U a) = f a := by
  refine (HolHom.valR_appLE q p ⊤ U le_top _ h).trans ?_
  rw [hq, Conv.valR_spMap_top]

def comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) : M.Sec where
  f j := ∑ i, constFn p _ (r i) * (σ i).f j
  compat j k := by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, res_constFn, res_constFn, (σ i).compat j k]
    ring

/- English proof (translation)
Simplify using `only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, comb, map_sum, map_mul]`.
-/
theorem valR_comb (p : X ⟶ Sp K) {M : LB X} {n : ℕ} (r : Fin n → K) (σ : Fin n → M.Sec) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) (j : M.ι) (h : ⊤ ≤ q ⁻¹ᵁ M.U j) :
    valR q _ ((comb p r σ).f j) = ∑ i, f (r i) * valR q _ ((σ i).f j) := by
  simp only [← valR_constFn p f q hq _ h, HolHom.valR_eq _ _ h, comb, map_sum, map_mul]

/- English proof (translation)
Conclude with `valR_comb p r σ f q hq (fun _ => j) (le_wchart h)`.
-/
theorem sval_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (r : Fin n → K) (σ : Fin n → SecP L π m) (f : K →+* R)
    (q : Sp R ⟶ X) (hq : q ≫ p = spMap f) {j : L.ι} (h : ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j) :
    ArcPts.sval (comb p r σ : SecP L π m) q j = ∑ i, f (r i) * ArcPts.sval (σ i) q j := by
  exact valR_comb p r σ f q hq (fun _ => j) (le_wchart h)

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ k, j = fun _ => k` from `⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩`. Use `TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_` and prove the remaining obligations. Take `⟨V, hV, hxV, hle⟩` from `exists_isAffineOpen_mem_and_subset (X := X) hx`. Take `⟨q, hq, hv⟩` from `Conv.exists_point_of_ringHom hV (RingHom.id _)`. Establish `hle' : V ≤ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j)` using `hle`.

Establish `e` using `h _ q j fun z hz => LB.wchart_le L (fun _ : Fin 1 => π) (fun _ => j) 0 (hle' (hq hz))`. Establish `e1` using `(hv _).symm.trans (HolHom.valR_res q hle' (s.f fun _ => j) hq)`. Establish `e2` using `(hv _).symm.trans (HolHom.valR_res q hle' (s'.f fun _ => j) hq)`. Conclude with `X.presheaf.germ_ext V hxV (homOfLE hle') (homOfLE hle') (e1.trans (e.trans e2.symm))`.
-/
theorem ext_sval {π : X ⟶ Z} {s s' : SecP L π m}
    (h : ∀ (R : Type) [CommRing R] (q : Sp R ⟶ X) (j : L.ι), ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
      ArcPts.sval s q j = ArcPts.sval s' q j) (j : Fin 1 → L.ι) : s.f j = s'.f j := by
  obtain ⟨j, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim _ _)⟩
  refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := exists_isAffineOpen_mem_and_subset (X := X) hx
  obtain ⟨q, hq, hv⟩ := Conv.exists_point_of_ringHom hV (RingHom.id _)
  have hle' : V ≤ LB.wchart L (fun _ : Fin 1 => π) (fun _ => j) := hle
  have e := h _ q j fun z hz => LB.wchart_le L (fun _ : Fin 1 => π) (fun _ => j) 0 (hle' (hq hz))
  have e1 := (hv _).symm.trans (HolHom.valR_res q hle' (s.f fun _ => j) hq)
  have e2 := (hv _).symm.trans (HolHom.valR_res q hle' (s'.f fun _ => j) hq)
  exact X.presheaf.germ_ext V hxV (homOfLE hle') (homOfLE hle') (e1.trans (e.trans e2.symm))

def Rep {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) : Prop :=
  ∀ (R : Type) [CommRing R] (f : K →+* R) (q : Sp R ⟶ X) (j : L.ι), q ≫ p = spMap f → ⊤ ≤ (q ≫ π) ⁻¹ᵁ L.U j →
    ArcPts.sval s q j = ∑ i, f (c i) * ArcPts.sval (σ i) q j

/- English proof (translation)
Introduce `_ _ f q _ hq h` and use `sval_comb p c σ f q hq h`.
-/
theorem rep_comb {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (c : Fin n → K) :
    Rep p σ (comb p c σ) c := fun _ _ f q _ hq h => sval_comb p c σ f q hq h

/- English proof (translation)
Use `⟨fun H => ext_sval fun R _ q j hj => ?_, fun H R _ f q j hq hj => ?_⟩` and prove the remaining obligations. Establish `hq : q ≫ p = spMap (Spec.preimage (q ≫ p)).hom` using `(Spec.map_preimage _).symm`. Conclude with `(H R _ q j hq hj).trans (sval_comb p c σ _ q hq hj).symm`. Conclude with `(congrArg (valR q _) (H _)).trans (sval_comb p c σ f q hq hj)`.
-/
theorem rep_iff {π : X ⟶ Z} (p : X ⟶ Sp K) {n : ℕ} (σ : Fin n → SecP L π m) (s : SecP L π m) (c : Fin n → K) :
    Rep p σ s c ↔ ∀ j, s.f j = (comb p c σ).f j := by
  refine ⟨fun H => ext_sval fun R _ q j hj => ?_, fun H R _ f q j hq hj => ?_⟩
  · have hq : q ≫ p = spMap (Spec.preimage (q ≫ p)).hom := (Spec.map_preimage _).symm
    exact (H R _ q j hq hj).trans (sval_comb p c σ _ q hq hj).symm
  · exact (congrArg (valR q _) (H _)).trans (sval_comb p c σ f q hq hj)

/- English proof (translation)
Substitute `hπ hp` using the available equality. Take `⟨s, -, hs⟩` from `exists_pull s' e.inv (π' := π) (e.inv_hom_id_assoc π)`. Establish `key : ∀ c, Rep (e.hom ≫ p) σ' s' c ↔ Rep p σ s c` using `fun c => by`. Prove the components needed by the constructor for the conclusion. Introduce `h R _ f q j hq hj`.

Establish `hj' : ⊤ ≤ ((q ≫ e.inv) ≫ e.hom ≫ π) ⁻¹ᵁ L.U j` using `by simpa using hj`. Rewrite using `[hs R q j hj, h R f _ j (by simpa using hq) hj']`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hσ i R _ j hj', Category.assoc, e.inv_hom_id, Category.comp_id]`. Introduce `h R _ f q j hq hj`.

Establish `hj' : ⊤ ≤ ((q ≫ e.hom) ≫ π) ⁻¹ᵁ L.U j` using `by simpa using hj`. Use `h R f (q ≫ e.hom) j (by simpa using hq) hj'` as an intermediate fact. Rewrite `this` using `[hs R _ j hj', Category.assoc, e.hom_inv_id, Category.comp_id]`. Rewrite using `[this]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hσ i R _ j hj]`.

Simplify using `only [key]`. Conclude with `H s`.
-/
theorem rep_transport {π : X ⟶ Z} {p : X ⟶ Sp K} {n : ℕ} {σ : Fin n → SecP L π m} (e : Y ≅ X) {π' : Y ⟶ Z}
    {p' : Y ⟶ Sp K} (hπ : e.hom ≫ π = π') (hp : e.hom ≫ p = p') {σ' : Fin n → SecP L π' m}
    (hσ : ∀ i (R : Type) [CommRing R] (q : Sp R ⟶ Y) (j : L.ι), ⊤ ≤ (q ≫ π') ⁻¹ᵁ L.U j →
      ArcPts.sval (σ' i) q j = ArcPts.sval (σ i) (q ≫ e.hom) j)
    (H : ∀ s, ∃! c, Rep p σ s c) (s' : SecP L π' m) : ∃! c, Rep p' σ' s' c := by
  subst hπ hp
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (π' := π) (e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ p) σ' s' c ↔ Rep p σ s c := fun c => by
    constructor
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.inv) ≫ e.hom ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      rw [hs R q j hj, h R f _ j (by simpa using hq) hj']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hσ i R _ j hj', Category.assoc, e.inv_hom_id, Category.comp_id]
    · intro h R _ f q j hq hj
      have hj' : ⊤ ≤ ((q ≫ e.hom) ≫ π) ⁻¹ᵁ L.U j := by simpa using hj
      have := h R f (q ≫ e.hom) j (by simpa using hq) hj'
      rw [hs R _ j hj', Category.assoc, e.hom_inv_id, Category.comp_id] at this
      rw [this]
      exact Finset.sum_congr rfl fun i _ => by rw [hσ i R _ j hj]
  simp only [key]
  exact H s

open Out in

/- English proof (translation)
Take `⟨V, hV, b, hb⟩` from `hS S P n hn x`. Set `W` to `overRes (T := baseOver S) V`. Establish `key : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S), ⊤ ≤ y ⁻¹ᵁ V → ∃ (k : pullback P.A.hom y ⟶ (W ⊗ P.A).left) (β : Fin (n ^ P.g) → SecP P.L (pullback.fst P.A.hom y) n), k ≫ (snd W P.A).left = pullback.fst _ _ ∧ (∀ i (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (j : P.L.ι), …` using `n) (p := (snd W P.A).left) (b i) (q ≫ k) j) ∧ ∀ s, ∃! c, Rep (pullback.snd P.A.hom y) β s c := by`. Introduce `R _ y hy`. Set `t : Sp R ⟶ W.left` to `IsOpenImmersion.lift V.ι y (by`.

Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `V.range_ι.ge (hy (x := z) trivial))`. Establish `ht : (baseAt t).hom = y` using `by show t ≫ V.ι ≫ 𝟙 _ = y`. Rewrite using `[Category.comp_id]`. Conclude with `IsOpenImmersion.lift_fac _ _ _`.

Establish `hp : IsPullback (pullback.snd P.A.hom y) (pullback.fst P.A.hom y) (baseAt t).hom P.A.hom` using `ht ▸ (IsPullback.of_hasPullback P.A.hom y).flip`. Set `e : pullback P.A.hom y ≅ (baseAt t ⊗ P.A).left` to `hp.isoPullback`. Establish `e₁ : e.hom ≫ (snd (baseAt t) P.A).left = pullback.fst _ _` using `hp.isoPullback_hom_snd`. Establish `e₂ : e.hom ≫ (fst (baseAt t) P.A).left = pullback.snd _ _` using `hp.isoPullback_hom_fst`. Establish `e₃ : (homAt t ▷ P.A).left ≫ (snd W P.A).left = (snd (baseAt t) P.A).left` using `congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)`.

Use `choose b' hb0 hb' using fun i => exists_pull (π := (snd W P.A).left) (m := n) (b i) (homAt t ▷ P.A).left e₃`. Use `choose β _ hβ using fun i => exists_pull (b' i) e.hom e₁`. Take `⟨hli, hsp⟩` from `hb R t b' (fun i j => hb0 i j _)`. Use `⟨e.hom ≫ (homAt t ▷ P.A).left, β, (Category.assoc _ _ _).trans ((congrArg _ e₃).trans e₁), fun i C _ q j hj => ?_, rep_transport (p := (fst (baseAt t) P.A).left) e e₁ e₂ hβ fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[hβ i C q j hj, hb' i C _ j (by rw [Category.assoc, e₁]; exact hj), Category.assoc]`.

Establish `bij` using `ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv`. Establish `key : ∀ c : Fin (n ^ P.g) → R, Rep (fst (baseAt t) P.A).left b' s c ↔ ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) • (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s` using `fun c => by`. Establish `ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) • (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j = (comb (K` using `R) (fst (baseAt t) P.A).left c b').f j := fun j => by`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Both sides reduce to the same expression.

Rewrite using `[rep_iff]`. Conclude with `⟨fun h => Subtype.ext (funext fun j => (ev j).trans (h j).symm), fun h j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)⟩`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))`. Use `choose a ha using fun i => bij.2 (r i)`. Take `rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) = r` from `funext ha`.

Use `⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩` and prove the remaining obligations. Conclude with `Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i`. Use `choose k β hk hβ hr using key`. Use `⟨V, hV, _, β, fun R _ y hy R' _ y' hy' C _ q q' i j hq hj => ?_, hr⟩` and prove the remaining obligations. Establish `hm : Mono (snd W P.A).left`.

Establish `: Mono W.hom` using `inferInstanceAs (Mono (V.ι ≫ 𝟙 S))`. Conclude with `inferInstanceAs (Mono (pullback.snd W.hom P.A.hom))`. Rewrite using `[hβ R y hy i C q j hj, hβ R' y' hy' i C q' j (hq ▸ hj)]`. Use `congr 1`. Rewrite using `[← cancel_mono (snd W P.A).left, Category.assoc, Category.assoc, hk, hk, hq]`.
-/
theorem exists_frame (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ)
    (hn : 1 ≤ n) (x : S) : ∃ V : S.Opens, x ∈ V ∧ ∃ (N : ℕ) (β : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S),
      ⊤ ≤ y ⁻¹ᵁ V → Fin N → SecP P.L (pullback.fst P.A.hom y) n),
      (∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (R' : Type) [CommRing R'] (y' : Sp R' ⟶ S)
        (hy' : ⊤ ≤ y' ⁻¹ᵁ V) (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (q' : Sp C ⟶ pullback P.A.hom y')
        (i : Fin N) (j : P.L.ι), q ≫ pullback.fst _ _ = q' ≫ pullback.fst _ _ →
        ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j → ArcPts.sval (β R y hy i) q j = ArcPts.sval (β R' y' hy' i) q' j) ∧
      ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S) (hy : ⊤ ≤ y ⁻¹ᵁ V) (s : SecP P.L (pullback.fst P.A.hom y) n),
        ∃! c, Rep (pullback.snd P.A.hom y) (β R y hy) s c := by
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn x
  let W := overRes (T := baseOver S) V
  have key : ∀ (R : Type) [CommRing R] (y : Sp R ⟶ S), ⊤ ≤ y ⁻¹ᵁ V →
      ∃ (k : pullback P.A.hom y ⟶ (W ⊗ P.A).left) (β : Fin (n ^ P.g) → SecP P.L (pullback.fst P.A.hom y) n),
        k ≫ (snd W P.A).left = pullback.fst _ _ ∧
        (∀ i (C : Type) [CommRing C] (q : Sp C ⟶ pullback P.A.hom y) (j : P.L.ι),
          ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ P.L.U j →
          ArcPts.sval (β i) q j = ArcPts.sval (m := n) (p := (snd W P.A).left) (b i) (q ≫ k) j) ∧
        ∀ s, ∃! c, Rep (pullback.snd P.A.hom y) β s c := by
    intro R _ y hy
    let t : Sp R ⟶ W.left := IsOpenImmersion.lift V.ι y (by
      rintro _ ⟨z, rfl⟩
      exact V.range_ι.ge (hy (x := z) trivial))
    have ht : (baseAt t).hom = y := by
      show t ≫ V.ι ≫ 𝟙 _ = y
      rw [Category.comp_id]
      exact IsOpenImmersion.lift_fac _ _ _
    have hp : IsPullback (pullback.snd P.A.hom y) (pullback.fst P.A.hom y) (baseAt t).hom P.A.hom :=
      ht ▸ (IsPullback.of_hasPullback P.A.hom y).flip
    let e : pullback P.A.hom y ≅ (baseAt t ⊗ P.A).left := hp.isoPullback
    have e₁ : e.hom ≫ (snd (baseAt t) P.A).left = pullback.fst _ _ := hp.isoPullback_hom_snd
    have e₂ : e.hom ≫ (fst (baseAt t) P.A).left = pullback.snd _ _ := hp.isoPullback_hom_fst
    have e₃ : (homAt t ▷ P.A).left ≫ (snd W P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    choose b' hb0 hb' using fun i => exists_pull (π := (snd W P.A).left) (m := n) (b i) (homAt t ▷ P.A).left e₃
    choose β _ hβ using fun i => exists_pull (b' i) e.hom e₁
    obtain ⟨hli, hsp⟩ := hb R t b' (fun i j => hb0 i j _)
    refine ⟨e.hom ≫ (homAt t ▷ P.A).left, β, (Category.assoc _ _ _).trans ((congrArg _ e₃).trans e₁), fun i C _ q j hj => ?_,
      rep_transport (p := (fst (baseAt t) P.A).left) e e₁ e₂ hβ fun s => ?_⟩
    · rw [hβ i C q j hj, hb' i C _ j (by rw [Category.assoc, e₁]; exact hj), Category.assoc]
    have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv
    have key : ∀ c : Fin (n ^ P.g) → R, Rep (fst (baseAt t) P.A).left b' s c ↔
        ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
      have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c i)) •
          (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
          (comb (K := R) (fst (baseAt t) P.A).left c b').f j := fun j => by
        rw [Submodule.coe_sum, Finset.sum_apply]
        rfl
      rw [rep_iff]
      exact ⟨fun h => Subtype.ext (funext fun j => (ev j).trans (h j).symm),
        fun h j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)⟩
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
    choose a ha using fun i => bij.2 (r i)
    obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (a i)) = r := funext ha
    refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
    exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i
  choose k β hk hβ hr using key
  refine ⟨V, hV, _, β, fun R _ y hy R' _ y' hy' C _ q q' i j hq hj => ?_, hr⟩
  have hm : Mono (snd W P.A).left := by
    have : Mono W.hom := inferInstanceAs (Mono (V.ι ≫ 𝟙 S))
    exact inferInstanceAs (Mono (pullback.snd W.hom P.A.hom))
  rw [hβ R y hy i C q j hj, hβ R' y' hy' i C q' j (hq ▸ hj)]
  congr 1
  rw [← cancel_mono (snd W P.A).left, Category.assoc, Category.assoc, hk, hk, hq]

end GlobalTheory.FibreFrame
