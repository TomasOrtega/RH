import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SharpRelations
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SharpFamRel

section Group

/- English proof (translation)
Establish `hs : Surjective f` using `⟨fun y => by`. Take `⟨z⟩` from `‹Nonempty S'›`. Conclude with `⟨z, Subsingleton.elim _ _⟩⟩`. Establish `: Flat h` using `MorphismProperty.of_isPullback H.flip inferInstance`. Establish `: Surjective h` using `MorphismProperty.of_isPullback H.flip hs`.

Conclude with `Flat.epi_of_flat_of_surjective h`.
-/
theorem epi_of_isPullback {K : Type} [Field K] {S' : Scheme.{0}} {f : S' ⟶ Sp K} [Nonempty S'] {X₀ X : Scheme.{0}}
    {p₀ : X₀ ⟶ Sp K} {p : X ⟶ S'} {h : X ⟶ X₀} (H : IsPullback h p p₀ f) : Epi h := by
  have hs : Surjective f := ⟨fun y => by
    obtain ⟨z⟩ := ‹Nonempty S'›
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have : Flat h := MorphismProperty.of_isPullback H.flip inferInstance
  have : Surjective h := MorphismProperty.of_isPullback H.flip hs
  exact Flat.epi_of_flat_of_surjective h

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
  (h : IsGrpPullback G' G f φ)

section Points

variable {T : Over S} {T' : Over S'} (U : Over.mk (T'.hom ≫ f) ⟶ T)

/- English proof (translation)
Substitute `e` using the available equality. Establish `e' : x'.left ≫ φ = y'.left ≫ φ` using `congrArg CommaMorphism.left (hx.trans hy.symm)`. Conclude with `Over.OverMorphism.ext (h.1.hom_ext e' (by rw [Over.w x', Over.w y']))`.
-/
theorem eq_up {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) (hy : pushPt h.1.w y' = U ≫ y)
    (e : x = y) : x' = y' := by
  subst e
  have e' : x'.left ≫ φ = y'.left ≫ φ := congrArg CommaMorphism.left (hx.trans hy.symm)
  exact Over.OverMorphism.ext (h.1.hom_ext e' (by rw [Over.w x', Over.w y']))

/- English proof (translation)
Substitute `e` using the available equality. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[← cancel_epi U.left]`. Simplify using `using congrArg CommaMorphism.left (hx.symm.trans hy)`.
-/
theorem eq_down (hU : Epi U.left) {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x)
    (hy : pushPt h.1.w y' = U ≫ y) (e : x' = y') : x = y := by
  subst e
  apply Over.OverMorphism.ext
  rw [← cancel_epi U.left]
  simpa using congrArg CommaMorphism.left (hx.symm.trans hy)

/- English proof (translation)
Establish `hm` using `h.2 T' x' y' (pushPt h.1.w x') (pushPt h.1.w y') rfl rfl`. Rewrite `hm` using `[hx, hy, ← MonObj.comp_mul]`. Conclude with `Over.OverMorphism.ext hm.symm`.
-/
theorem push_mul {x' y' : T' ⟶ G'} {x y : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) (hy : pushPt h.1.w y' = U ≫ y) :
    pushPt h.1.w (x' * y') = U ≫ (x * y) := by
  have hm := h.2 T' x' y' (pushPt h.1.w x') (pushPt h.1.w y') rfl rfl
  rw [hx, hy, ← MonObj.comp_mul] at hm
  exact Over.OverMorphism.ext hm.symm

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Establish `hx' : x'.left ≫ φ = U.left ≫ x.left` using `congrArg CommaMorphism.left hx`. Simplify using `only [pushPt, Over.homMk_left, Over.comp_left]`. Rewrite using `[Category.assoc, ha, ← Category.assoc, hx', Category.assoc]`.
-/
theorem push_comp {x' : T' ⟶ G'} {x : T ⟶ G} (hx : pushPt h.1.w x' = U ≫ x) {a' : G' ⟶ G'} {a : G ⟶ G}
    (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w (x' ≫ a') = U ≫ x ≫ a := by
  apply Over.OverMorphism.ext
  have hx' : x'.left ≫ φ = U.left ≫ x.left := congrArg CommaMorphism.left hx
  simp only [pushPt, Over.homMk_left, Over.comp_left]
  rw [Category.assoc, ha, ← Category.assoc, hx', Category.assoc]

end Points

def selfMap : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `[pushPt, selfMap]`.
-/
theorem push_id : pushPt h.1.w (𝟙 G') = selfMap h ≫ 𝟙 G := by
  apply Over.OverMorphism.ext
  simp [pushPt, selfMap]

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify `ha` using `[pushPt, selfMap]`.
-/
theorem push_end {a' : G' ⟶ G'} {a : G ⟶ G} (ha : a'.left ≫ φ = φ ≫ a.left) : pushPt h.1.w a' = selfMap h ≫ a := by
  apply Over.OverMorphism.ext
  simpa [pushPt, selfMap] using ha

end Group

def baseMap {S S' : Scheme.{0}} (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S :=
  Over.homMk f ((Category.comp_id _).trans (Category.id_comp _).symm)

/- English proof (translation)
Use `Finset.induction_on s (by simp) fun i s hi ih => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]`.
-/
theorem zpow_finsetSum {G I : Type} [CommGroup G] (x : G) (s : Finset I) (n : I → ℤ) :
    x ^ (∑ i ∈ s, n i) = ∏ i ∈ s, x ^ n i := by
  classical
  refine Finset.induction_on s (by simp) fun i s hi ih => ?_
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

/- English proof (translation)
Use `choose Z Y ψ q x hpb hx hψ using H`. Set `inc : (∐ fun p : D => Z p.1 p.2) ⟶ T.left` to `Sigma.desc fun p => ψ p.1 p.2`. Establish `hinc : inc ≫ f.left = inc ≫ g.left`. Use `Sigma.hom_ext _ _ fun p => ?_` and prove the remaining obligations. Simplify using `only [inc, Sigma.ι_desc_assoc]`.

Conclude with `hψ p.1 p.2`. Establish `hsub : T.hom.base ⁻¹' D ⊆ Set.range inc.base`. Introduce `a ha`. Take `⟨y, hy⟩` from `hx _ ha`. Take `⟨z, hz₁, -⟩` from `Scheme.Pullback.exists_preimage_pullback a y hy.symm`.

Use `⟨(Sigma.ι (fun p : D => Z p.1 p.2) ⟨_, ha⟩).base ((hpb _ ha).isoPullback.inv.base z), ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_desc]`. Use `show ((hpb _ ha).isoPullback.inv ≫ ψ _ ha) z = a`. Rewrite using `[IsPullback.isoPullback_inv_fst]`. Conclude with `hz₁`.

Establish `: IsDominant inc` using `⟨((hD.preimage hT).mono hsub)⟩`. Conclude with `Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w f, Over.w g]) inc hinc)`.
-/
theorem ext_of_dense {S : Scheme.{0}} {T G : Over S} [IsReduced T.left] (hT : IsOpenMap T.hom) [IsSeparated G.hom]
    (f g : T ⟶ G) {D : Set S} (hD : Dense D)
    (H : ∀ p ∈ D, ∃ (Z Y : Scheme.{0}) (ψ : Z ⟶ T.left) (q : Z ⟶ Y) (x : Y ⟶ S), IsPullback ψ q T.hom x ∧
      p ∈ Set.range x ∧ ψ ≫ f.left = ψ ≫ g.left) : f = g := by
  choose Z Y ψ q x hpb hx hψ using H
  let inc : (∐ fun p : D => Z p.1 p.2) ⟶ T.left := Sigma.desc fun p => ψ p.1 p.2
  have hinc : inc ≫ f.left = inc ≫ g.left := by
    refine Sigma.hom_ext _ _ fun p => ?_
    simp only [inc, Sigma.ι_desc_assoc]
    exact hψ p.1 p.2
  have hsub : T.hom.base ⁻¹' D ⊆ Set.range inc.base := by
    intro a ha
    obtain ⟨y, hy⟩ := hx _ ha
    obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback a y hy.symm
    refine ⟨(Sigma.ι (fun p : D => Z p.1 p.2) ⟨_, ha⟩).base ((hpb _ ha).isoPullback.inv.base z), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_desc]
    show ((hpb _ ha).isoPullback.inv ≫ ψ _ ha) z = a
    rw [IsPullback.isoPullback_inv_fst]
    exact hz₁
  have : IsDominant inc := ⟨((hD.preimage hT).mono hsub)⟩
  exact Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom (by rw [Over.w f, Over.w g]) inc hinc)

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

def NatEnd (F : ∀ {S : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s), t.A ⟶ t.A) : Prop :=
  ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} (t' : TObj g k J b s') (t : TObj g k J b s) {f : S' ⟶ S}
    {φ : t'.A.left ⟶ t.A.left} (h : IsGrpPullback t'.A t.A f φ),
    (∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left) → pushPt h.1.w (F t') = selfMap h ≫ F t

def NatPt (F : ∀ {S : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s), Out.baseOver S ⟶ t.A) : Prop :=
  ∀ {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} (t' : TObj g k J b s') (t : TObj g k J b s) {f : S' ⟶ S}
    {φ : t'.A.left ⟶ t.A.left} (h : IsGrpPullback t'.A t.A f φ),
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) →
    (∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left) → pushPt h.1.w (F t') = baseMap f ≫ F t

variable {em : o →+* ℂ} {C : TObj g k J b (spMap em) → Prop} {S : Scheme.{0}} {s : S ⟶ Sp o}

/- English proof (translation)
Use `t.ab.smooth` as an intermediate fact. Use `t.ab.proper` as an intermediate fact. Establish `: IsReduced t.A.left` using `GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom`. Use `ext_of_dense t.A.hom.isOpenMap (F t) (G t) hD ?_` and prove the remaining obligations. Introduce and unpack `p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, -, -, ⟨φx, hx, -, -, hax⟩, ⟨φ0, h0, -, -, ha0⟩, ⟨φc, hc, -, -, hac⟩, hC⟩`.

Establish `: Nonempty (Sp ℂ)` using `inferInstanceAs (Nonempty (PrimeSpectrum ℂ))`. Establish `e0 : F t₀ = G t₀` using `eq_down hc (selfMap hc) (epi_of_isPullback hc.1) (hF tc t₀ hc hac) (hG tc t₀ hc hac) (H tc hC)`. Establish `e1 : F tx = G tx` using `eq_up h0 (selfMap h0) (hF tx t₀ h0 ha0) (hG tx t₀ h0 ha0) e0`. Use `⟨tx.A.left, Sp K, φx, tx.A.hom, x, hx.1, hp, ?_⟩` and prove the remaining obligations. Establish `k1 : (F tx).left ≫ φx = φx ≫ (F t).left` using `congrArg CommaMorphism.left (hF tx t hx hax)`.

Establish `k2 : (G tx).left ≫ φx = φx ≫ (G t).left` using `congrArg CommaMorphism.left (hG tx t hx hax)`. Rewrite using `[← k1, ← k2, e1]`.
-/
theorem transfer_end [IsReduced S] {F G : ∀ {S : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s), t.A ⟶ t.A}
    (hF : NatEnd F) (hG : NatEnd G) (H : ∀ tc, C tc → F tc = G tc) (t : TObj g k J b s)
    (hD : Dense (fromSet em C t)) : F t = G t := by
  have := t.ab.smooth
  have := t.ab.proper
  have : IsReduced t.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced t.A.hom
  refine ext_of_dense t.A.hom.isOpenMap (F t) (G t) hD ?_
  rintro p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, -, -, ⟨φx, hx, -, -, hax⟩, ⟨φ0, h0, -, -, ha0⟩,
    ⟨φc, hc, -, -, hac⟩, hC⟩
  have : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  have e0 : F t₀ = G t₀ :=
    eq_down hc (selfMap hc) (epi_of_isPullback hc.1) (hF tc t₀ hc hac) (hG tc t₀ hc hac) (H tc hC)
  have e1 : F tx = G tx := eq_up h0 (selfMap h0) (hF tx t₀ h0 ha0) (hG tx t₀ h0 ha0) e0
  refine ⟨tx.A.left, Sp K, φx, tx.A.hom, x, hx.1, hp, ?_⟩
  have k1 : (F tx).left ≫ φx = φx ≫ (F t).left := congrArg CommaMorphism.left (hF tx t hx hax)
  have k2 : (G tx).left ≫ φx = φx ≫ (G t).left := congrArg CommaMorphism.left (hG tx t hx hax)
  rw [← k1, ← k2, e1]

/- English proof (translation)
Use `t.ab.proper` as an intermediate fact. Establish `hbase : (Out.baseOver S).hom = 𝟙 S` using `rfl`. Establish `: IsReduced (Out.baseOver S).left` using `‹IsReduced S›`. Use `ext_of_dense (by rw [hbase]; exact IsOpenMap.id) (F t) (G t) hD ?_` and prove the remaining obligations. Introduce and unpack `p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, -, -, ⟨φx, hx, -, hpx, hax⟩, ⟨φ0, h0, -, hp0, ha0⟩, ⟨φc, hc, -, hpc, hac⟩, hC⟩`.

Establish `hepi : Epi (baseMap (S'` using `Sp ℂ) (spMap j)).left := by`. Establish `hs : Surjective (spMap j)` using `⟨fun y => by`. Take `⟨z⟩ : Nonempty (Sp ℂ)` from `inferInstanceAs (Nonempty (PrimeSpectrum ℂ))`. Conclude with `⟨z, Subsingleton.elim _ _⟩⟩`. Conclude with `Flat.epi_of_flat_of_surjective (spMap j)`.

Establish `e0 : F t₀ = G t₀` using `eq_down hc (baseMap (spMap j)) hepi (hF tc t₀ hc hpc hac) (hG tc t₀ hc hpc hac) (H tc hC)`. Establish `e1 : F tx = G tx` using `eq_up h0 (baseMap (spMap i)) (hF tx t₀ h0 hp0 ha0) (hG tx t₀ h0 hp0 ha0) e0`. Use `⟨Sp K, Sp K, x, 𝟙 _, x, by rw [hbase]; exact IsPullback.of_id_snd, hp, ?_⟩` and prove the remaining obligations. Establish `k1 : (F tx).left ≫ φx = x ≫ (F t).left` using `congrArg CommaMorphism.left (hF tx t hx hpx hax)`. Establish `k2 : (G tx).left ≫ φx = x ≫ (G t).left` using `congrArg CommaMorphism.left (hG tx t hx hpx hax)`.

Rewrite using `[← k1, ← k2, e1]`.
-/
theorem transfer_pt [IsReduced S]
    {F G : ∀ {S : Scheme.{0}} {s : S ⟶ Sp o} (t : TObj g k J b s), Out.baseOver S ⟶ t.A}
    (hF : NatPt F) (hG : NatPt G) (H : ∀ tc, C tc → F tc = G tc) (t : TObj g k J b s)
    (hD : Dense (fromSet em C t)) : F t = G t := by
  have := t.ab.proper
  have hbase : (Out.baseOver S).hom = 𝟙 S := rfl
  have : IsReduced (Out.baseOver S).left := ‹IsReduced S›
  refine ext_of_dense (by rw [hbase]; exact IsOpenMap.id) (F t) (G t) hD ?_
  rintro p ⟨K, _, x, hp, K₀, _, β, i, j, t₀, tx, tc, -, -, ⟨φx, hx, -, hpx, hax⟩, ⟨φ0, h0, -, hp0, ha0⟩,
    ⟨φc, hc, -, hpc, hac⟩, hC⟩
  have hepi : Epi (baseMap (S' := Sp ℂ) (spMap j)).left := by
    have hs : Surjective (spMap j) := ⟨fun y => by
      obtain ⟨z⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
      exact ⟨z, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective (spMap j)
  have e0 : F t₀ = G t₀ :=
    eq_down hc (baseMap (spMap j)) hepi (hF tc t₀ hc hpc hac) (hG tc t₀ hc hpc hac) (H tc hC)
  have e1 : F tx = G tx := eq_up h0 (baseMap (spMap i)) (hF tx t₀ h0 hp0 ha0) (hG tx t₀ h0 hp0 ha0) e0
  refine ⟨Sp K, Sp K, x, 𝟙 _, x, by rw [hbase]; exact IsPullback.of_id_snd, hp, ?_⟩
  have k1 : (F tx).left ≫ φx = x ≫ (F t).left := congrArg CommaMorphism.left (hF tx t hx hpx hax)
  have k2 : (G tx).left ≫ φx = x ≫ (G t).left := congrArg CommaMorphism.left (hG tx t hx hpx hax)
  rw [← k1, ← k2, e1]

/- English proof (translation)
Take `⟨pr, hpr, huniq, -, hact, hpt⟩` from `H`. Establish `ext : ∀ {T : Over S} (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y` using `fun x y hxy => (huniq _ fun u => y ≫ pr u).unique hxy fun _ => rfl`. Establish `pre : ∀ {T : Over S} (y : T ⟶ t.A) (n : Fin 8 → ℤ), y ≫ ∏ v, pr v ^ n v = ∏ v, (y ≫ pr v) ^ n v`. Introduce `T y n`. Set `e : (t.A ⟶ c.A) →* (T ⟶ c.A)` to `MonoidHom.mk' (y ≫ ·) (MonObj.comp_mul y)`.

Conclude with `(map_prod e _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow e _ _)`. Establish `hact' : ∀ j u, t.act j ≫ pr u = ∏ v, pr v ^ a j u v` using `fun j u => by rw [hact, List.prod_ofFn]`. Use `⟨fun j j' j'' hm => ext _ _ fun u => ?_, fun j j' j'' hm => ext _ _ fun u => ?_, fun j hj => ext _ _ fun u => ?_, fun j i => ext _ _ fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[hact', Category.assoc, hact', pre]`. Simplify using `only [hact', ← Finset.prod_zpow, ← zpow_mul]`.

Rewrite using `[hm, Finset.prod_comm]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, zpow_finsetSum]`. Conclude with `Finset.prod_congr rfl fun w _ => by rw [mul_comm]`. Use `hpr u` as an intermediate fact.

Rewrite using `[MonObj.mul_comp, hact', hact', hact', hm, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun v _ => by rw [Matrix.add_apply, zpow_add]`. Rewrite using `[hact', hj, Category.id_comp, Finset.prod_eq_single u (fun v _ hv => by rw [Matrix.one_apply_ne hv.symm, zpow_zero]) (fun hn => absurd (Finset.mem_univ u) hn), Matrix.one_apply_eq, zpow_one]`. Use `hpr u` as an intermediate fact. Establish `hq : ∀ i v, t.pt i ≫ pr v = c.lev (bas (Pi.single i 1) v)` using `fun i v => Over.OverMorphism.ext (hpt i v)`.

Set `M : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (𝟙_ (Over S) ⟶ c.A)` to `MonoidHom.mk' (fun w => c.lev w.toAdd) fun x y => c.lev_add _ _`. Establish `levsum : ∀ (ι' : Type) [Fintype ι'] (n : ι' → ℤ) (w : ι' → (Fin h ⊕ Fin h → ℤ)), c.lev (∑ x, n x • w x) = ∏ x, c.lev (w x) ^ n x`. Introduce `ι' _ n w`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ofAdd_sum, map_prod]`.

Conclude with `Finset.prod_congr rfl fun x _ => by rw [ofAdd_zsmul, map_zpow]; rfl`. Establish `key : ∀ n : Fin (2 * g) → ℤ, ∑ i', n i' • bas (Pi.single i' 1) = bas n`. Introduce `n`. Use `conv_rhs => rw [← Finset.univ_sum_single n]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Rewrite using `[← map_zsmul]`. Use `congr 1`. Use extensionality with `m`. Rewrite using `[Pi.smul_apply, Pi.single_apply, Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `kv` using `congrFun (key (bas.symm fun u => ∑ v, a j u v • bas (Pi.single i 1) v)) u`. Rewrite `kv` using `[LinearEquiv.apply_symm_apply, Finset.sum_apply]`. Simplify using `only [Pi.smul_apply] at kv`. Set `post : (Out.baseOver S ⟶ t.A) →* (Out.baseOver S ⟶ c.A)` to `MonoidHom.mk' (· ≫ pr u) fun x y => MonObj.mul_comp x y (pr u)`.

Rewrite using `[Category.assoc, hact', pre]`. Rewrite using `[show (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod ≫ pr u = post (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod from rfl, map_list_prod, List.map_ofFn, List.prod_ofFn]`. Simplify using `only [Function.comp_apply, map_zpow]`. Simplify using `only [post, MonoidHom.mk'_apply, hq]`. Rewrite using `[← levsum, ← levsum, kv]`.
-/
theorem rel_of_isSharp {h : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {a : J → Matrix (Fin 8) (Fin 8) ℤ}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} {t : TObj g k J b s}
    {c : SiegPre h k (b.ζ : o) s} (H : IsSharp W a bas t c) :
    (∀ j j' j'', a j'' = a j * a j' → t.act j'' = t.act j' ≫ t.act j) ∧
    (∀ j j' j'', a j'' = a j + a j' → t.act j'' = t.act j * t.act j') ∧ (∀ j, a j = 1 → t.act j = 𝟙 t.A) ∧
    ∀ j i, t.pt i ≫ t.act j =
      (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod := by
  obtain ⟨pr, hpr, huniq, -, hact, hpt⟩ := H
  have ext : ∀ {T : Over S} (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y :=
    fun x y hxy => (huniq _ fun u => y ≫ pr u).unique hxy fun _ => rfl
  have pre : ∀ {T : Over S} (y : T ⟶ t.A) (n : Fin 8 → ℤ), y ≫ ∏ v, pr v ^ n v = ∏ v, (y ≫ pr v) ^ n v := by
    intro T y n
    let e : (t.A ⟶ c.A) →* (T ⟶ c.A) := MonoidHom.mk' (y ≫ ·) (MonObj.comp_mul y)
    exact (map_prod e _ _).trans (Finset.prod_congr rfl fun v _ => map_zpow e _ _)
  have hact' : ∀ j u, t.act j ≫ pr u = ∏ v, pr v ^ a j u v := fun j u => by rw [hact, List.prod_ofFn]
  refine ⟨fun j j' j'' hm => ext _ _ fun u => ?_, fun j j' j'' hm => ext _ _ fun u => ?_,
    fun j hj => ext _ _ fun u => ?_, fun j i => ext _ _ fun u => ?_⟩
  · rw [hact', Category.assoc, hact', pre]
    simp only [hact', ← Finset.prod_zpow, ← zpow_mul]
    rw [hm, Finset.prod_comm]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Matrix.mul_apply, zpow_finsetSum]
    exact Finset.prod_congr rfl fun w _ => by rw [mul_comm]
  · have := hpr u
    rw [MonObj.mul_comp, hact', hact', hact', hm, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => by rw [Matrix.add_apply, zpow_add]
  · rw [hact', hj, Category.id_comp, Finset.prod_eq_single u (fun v _ hv => by rw [Matrix.one_apply_ne hv.symm, zpow_zero])
      (fun hn => absurd (Finset.mem_univ u) hn), Matrix.one_apply_eq, zpow_one]
  · have := hpr u
    have hq : ∀ i v, t.pt i ≫ pr v = c.lev (bas (Pi.single i 1) v) := fun i v => Over.OverMorphism.ext (hpt i v)
    let M : Multiplicative (Fin h ⊕ Fin h → ℤ) →* (𝟙_ (Over S) ⟶ c.A) :=
      MonoidHom.mk' (fun w => c.lev w.toAdd) fun x y => c.lev_add _ _
    have levsum : ∀ (ι' : Type) [Fintype ι'] (n : ι' → ℤ) (w : ι' → (Fin h ⊕ Fin h → ℤ)),
        c.lev (∑ x, n x • w x) = ∏ x, c.lev (w x) ^ n x := by
      intro ι' _ n w
      calc c.lev (∑ x, n x • w x) = M (Multiplicative.ofAdd (∑ x, n x • w x)) := rfl
        _ = ∏ x, c.lev (w x) ^ n x := by
          rw [ofAdd_sum, map_prod]
          exact Finset.prod_congr rfl fun x _ => by rw [ofAdd_zsmul, map_zpow]; rfl
    have key : ∀ n : Fin (2 * g) → ℤ, ∑ i', n i' • bas (Pi.single i' 1) = bas n := by
      intro n
      conv_rhs => rw [← Finset.univ_sum_single n]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [← map_zsmul]
      congr 1
      ext m
      rw [Pi.smul_apply, Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    have kv := congrFun (key (bas.symm fun u => ∑ v, a j u v • bas (Pi.single i 1) v)) u
    rw [LinearEquiv.apply_symm_apply, Finset.sum_apply] at kv
    simp only [Pi.smul_apply] at kv
    let post : (Out.baseOver S ⟶ t.A) →* (Out.baseOver S ⟶ c.A) :=
      MonoidHom.mk' (· ≫ pr u) fun x y => MonObj.mul_comp x y (pr u)
    rw [Category.assoc, hact', pre]
    rw [show (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod ≫ pr u =
      post (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod from rfl,
      map_list_prod, List.map_ofFn, List.prod_ofFn]
    simp only [Function.comp_apply, map_zpow]
    simp only [post, MonoidHom.mk'_apply, hq]
    rw [← levsum, ← levsum, kv]

end GlobalTheory.SharpFamRel

namespace GlobalTheory
open SharpFamRel

/- English proof (translation)
Introduce `h g W J a bas k o _ b em S _ s t hD`. Use `⟨fun j j' j'' hm => ?_, fun j j' j'' hm => ?_, fun j hj => ?_, fun j i => ?_⟩` and prove the remaining obligations. Use `transfer_end (F := fun t => t.act j'') (G := fun t => t.act j' ≫ t.act j) ?_ ?_ (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).1 j j' j'' hm) t hD` and prove the remaining obligations. Introduce `_ _ _ _ t' t _ _ hp hact`. Conclude with `push_end hp (hact j'')`.

Introduce `_ _ _ _ t' t _ _ hp hact`. Use `push_end hp ?_` and prove the remaining obligations. Simplify using `only [Over.comp_left, Category.assoc, hact j]`. Rewrite using `[← Category.assoc, hact j', Category.assoc]`. Use `transfer_end (F := fun t => t.act j'') (G := fun t => t.act j * t.act j') ?_ ?_ (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.1 j j' j'' hm) t hD` and prove the remaining obligations.

Introduce `_ _ _ _ t' t _ _ hp hact`. Conclude with `push_end hp (hact j'')`. Introduce `_ _ _ _ t' t _ _ hp hact`. Conclude with `push_mul hp (selfMap hp) (push_end hp (hact j)) (push_end hp (hact j'))`. Use `transfer_end (F := fun t => t.act j) (G := fun t => 𝟙 t.A) ?_ ?_ (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.2.1 j hj) t hD` and prove the remaining obligations.

Introduce `_ _ _ _ t' t _ _ hp hact`. Conclude with `push_end hp (hact j)`. Introduce `_ _ _ _ t' t _ _ hp _`. Conclude with `push_id hp`. Use `transfer_pt (F := fun t => t.pt i ≫ t.act j) (G := fun t => (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod) ?_ ?_ (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.2.2 j i) t hD` and prove the remaining obligations.

Introduce `_ _ _ _ t' t f _ hp hpt hact`. Conclude with `push_comp hp (baseMap f) (Over.OverMorphism.ext (hpt i)) (hact j)`. Introduce `_ S' _ _ t' t f _ hp hpt _`. Set `e : (Out.baseOver S' ⟶ t'.A) →* (Over.mk ((Out.baseOver S').hom ≫ f) ⟶ t.A)` to `MonoidHom.mk' (pushPt hp.1.w) fun x y => Over.OverMorphism.ext (hp.2 _ x y _ _ rfl rfl).symm`. Set `e2 : (Out.baseOver _ ⟶ t.A) →* (Over.mk ((Out.baseOver S').hom ≫ f) ⟶ t.A)` to `MonoidHom.mk' (baseMap f ≫ ·) (MonObj.comp_mul _)`.

Express the relevant statement in the definitionally equal form `e _ = e2 _`. Rewrite using `[map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]`. Use `congr 1`. Use `congrArg List.ofFn (funext fun i' => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, map_zpow]`.

Use `congr 1`. Conclude with `Over.OverMorphism.ext (hpt i')`.
-/
theorem sharp_family_relations : ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j' j'', a j'' = a j * a j' → t.act j'' = t.act j' ≫ t.act j) ∧ (∀ j j' j'', a j'' = a j + a j' → t.act j'' = t.act j * t.act j') ∧ (∀ j, a j = 1 → t.act j = 𝟙 t.A) ∧ ∀ j i, t.pt i ≫ t.act j = (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod := by
  intro h g W J a bas k o _ b em S _ s t hD
  refine ⟨fun j j' j'' hm => ?_, fun j j' j'' hm => ?_, fun j hj => ?_, fun j i => ?_⟩
  · refine transfer_end (F := fun t => t.act j'') (G := fun t => t.act j' ≫ t.act j) ?_ ?_
      (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).1 j j' j'' hm) t hD
    · intro _ _ _ _ t' t _ _ hp hact
      exact push_end hp (hact j'')
    · intro _ _ _ _ t' t _ _ hp hact
      refine push_end hp ?_
      simp only [Over.comp_left, Category.assoc, hact j]
      rw [← Category.assoc, hact j', Category.assoc]
  · refine transfer_end (F := fun t => t.act j'') (G := fun t => t.act j * t.act j') ?_ ?_
      (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.1 j j' j'' hm) t hD
    · intro _ _ _ _ t' t _ _ hp hact
      exact push_end hp (hact j'')
    · intro _ _ _ _ t' t _ _ hp hact
      exact push_mul hp (selfMap hp) (push_end hp (hact j)) (push_end hp (hact j'))
  · refine transfer_end (F := fun t => t.act j) (G := fun t => 𝟙 t.A) ?_ ?_
      (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.2.1 j hj) t hD
    · intro _ _ _ _ t' t _ _ hp hact
      exact push_end hp (hact j)
    · intro _ _ _ _ t' t _ _ hp _
      exact push_id hp
  · refine transfer_pt (F := fun t => t.pt i ≫ t.act j)
      (G := fun t => (List.ofFn fun i' => t.pt i' ^ bas.symm (fun u => ∑ v, a j u v • bas (Pi.single i 1) v) i').prod) ?_ ?_
      (fun tc hC => by obtain ⟨c, -, hc⟩ := hC; exact (rel_of_isSharp hc).2.2.2 j i) t hD
    · intro _ _ _ _ t' t f _ hp hpt hact
      exact push_comp hp (baseMap f) (Over.OverMorphism.ext (hpt i)) (hact j)
    · intro _ S' _ _ t' t f _ hp hpt _
      let e : (Out.baseOver S' ⟶ t'.A) →* (Over.mk ((Out.baseOver S').hom ≫ f) ⟶ t.A) :=
        MonoidHom.mk' (pushPt hp.1.w) fun x y => Over.OverMorphism.ext (hp.2 _ x y _ _ rfl rfl).symm
      let e2 : (Out.baseOver _ ⟶ t.A) →* (Over.mk ((Out.baseOver S').hom ≫ f) ⟶ t.A) :=
        MonoidHom.mk' (baseMap f ≫ ·) (MonObj.comp_mul _)
      change e _ = e2 _
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 1
      refine congrArg List.ofFn (funext fun i' => ?_)
      simp only [Function.comp_apply, map_zpow]
      congr 1
      exact Over.OverMorphism.ext (hpt i')

end GlobalTheory
end
