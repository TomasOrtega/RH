import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DkerOfKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Apply `UpperTheory.V.CA.d_ch_ker D` to reduce the goal to its premises. Establish `h1` using `(UpperTheory.V.CA.d_chS D A).1 ((1 : A) ⊗ₜ[A] x)`. Establish `hchi : D.chiS A ((1 : A) ⊗ₜ[A] x) = D.chi x`. Unfold `Det.chiS Det.chi`. Simplify using `[Algebra.TensorProduct.map_tmul]`.

Rewrite `h1` using `[hchi]`. Establish `he : Polynomial.aeval x (D.chi x) = Algebra.TensorProduct.lid A E (Polynomial.aeval ((1 : A) ⊗ₜ[A] x) (D.chi x))`. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Simplify using the standard rewrite rules. Rewrite using `[he]`.

Establish `key : ∀ w ∈ Submodule.span A ((fun z : E => (1 : A) ⊗ₜ[A] z) '' (D.CH : Set E)), Algebra.TensorProduct.lid A E w ∈ D.CH`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨c, hc, rfl⟩` from `hz`.

Simplify using `using hc`. Consider the case `zero => simpa using TwoSidedIdeal.zero_mem _`. Consider the case `add a b _ _ ha hb`. Rewrite using `[map_add]`. Conclude with `TwoSidedIdeal.add_mem _ ha hb`.

Consider the case `smul a z _ hz`. Rewrite using `[map_smul, Algebra.smul_def]`. Conclude with `TwoSidedIdeal.mul_mem_left _ _ _ hz`. Conclude with `key _ h1`.
-/
private theorem ch_ker {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E) :
    Polynomial.aeval x (D.chi x) ∈ D.ker := by
  apply UpperTheory.V.CA.d_ch_ker D
  have h1 := (UpperTheory.V.CA.d_chS D A).1 ((1 : A) ⊗ₜ[A] x)
  have hchi : D.chiS A ((1 : A) ⊗ₜ[A] x) = D.chi x := by
    unfold Det.chiS Det.chi
    simp [Algebra.TensorProduct.map_tmul]
  rw [hchi] at h1
  have he : Polynomial.aeval x (D.chi x) =
      Algebra.TensorProduct.lid A E (Polynomial.aeval ((1 : A) ⊗ₜ[A] x) (D.chi x)) := by
    rw [← Polynomial.aeval_algHom_apply]
    simp
  rw [he]
  have key : ∀ w ∈ Submodule.span A ((fun z : E => (1 : A) ⊗ₜ[A] z) '' (D.CH : Set E)),
      Algebra.TensorProduct.lid A E w ∈ D.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      simpa using hc
    | zero => simpa using TwoSidedIdeal.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add]
      exact TwoSidedIdeal.add_mem _ ha hb
    | smul a z _ hz =>
      rw [map_smul, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hz
  exact key _ h1

/- English proof (translation)
Establish `hk` using `(UpperTheory.V.CA.d_ker D.toDet y).2.2 hy h 1 le_rfl hn`. Establish `htr : D.toDet.tr (h * y) = D.toDet.lam 1 (h * y)`. Unfold `Det.tr Det.lam`. Both sides reduce to the same expression. Rewrite using `[← (UpperTheory.V.CA.d_toDet D (h * y)).2.2.1, htr, hk]`.
-/
private theorem tr_ker {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (hn : 1 ≤ n)
    {y : MonoidAlgebra A G} (hy : y ∈ D.toDet.ker) (h : MonoidAlgebra A G) : D.tr (h * y) = 0 := by
  have hk := (UpperTheory.V.CA.d_ker D.toDet y).2.2 hy h 1 le_rfl hn
  have htr : D.toDet.tr (h * y) = D.toDet.lam 1 (h * y) := by
    unfold Det.tr Det.lam
    rfl
  rw [← (UpperTheory.V.CA.d_toDet D (h * y)).2.2.1, htr, hk]

/- English proof (translation)
Unfold `q1El`. Rewrite using `[← Fin.prod_ofFn, map_list_prod, List.map_ofFn]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[MonoidAlgebra.coe_algebraMap]`.
-/
private theorem charpoly_element_eq_aeval_group_element {n : ℕ} {A G : Type} [CommRing A] [Group G] (g : G) (U : Fin n → A) :
    q1El g U = Polynomial.aeval (MonoidAlgebra.single g (1 : A)) (∏ i, (Polynomial.X - Polynomial.C (U i))) := by
  unfold q1El
  rw [← Fin.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  simp [MonoidAlgebra.coe_algebraMap]

private noncomputable def push {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G] (f : R →+* S)
    (φ : H →* G) : MonoidAlgebra R H →+* MonoidAlgebra S G :=
  (MonoidAlgebra.mapDomainRingHom S φ).comp (MonoidAlgebra.mapRingHom H f)

/- English proof (translation)
Simplify using `[push, MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapRingHom]`.
-/
private theorem push_single {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G] (f : R →+* S)
    (φ : H →* G) (g : H) (a : R) : push f φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) (f a) := by
  simp [push, MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapRingHom]

/- English proof (translation)
Establish `key : MonoidAlgebra.mapDomainRingHom (Polynomial S) φ (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C z) = MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z)`. Rewrite using `[map_sub]`. Use `congr 1`. Simplify using `[MonoidAlgebra.mapDomainRingHom]`. Proceed by induction on `z using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `single h s`. Simplify using `[MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapRingHom, MonoidAlgebra.mapDomain_single]`. Unfold `GDet.lam GDet.map GDet.comap GDet.chi`.

Simplify using `only`. Rewrite using `[MonoidHom.comp_apply]`. Use `erw [key]`.
-/
private theorem gDet_lam_map_comap_eq_lam_mapDomainRingHom {n : ℕ} {B S H G : Type} [CommRing B] [CommRing S] [Group H] [Group G]
    (D : GDet n B G) (a : B →+* S) (φ : H →* G) (i : ℕ) (z : MonoidAlgebra S H) :
    ((D.comap φ).map a).lam i z = (D.map a).lam i (MonoidAlgebra.mapDomainRingHom S φ z) := by
  have key : MonoidAlgebra.mapDomainRingHom (Polynomial S) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C z) =
      MonoidAlgebra.single 1 Polynomial.X -
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    rw [map_sub]
    congr 1
    · simp [MonoidAlgebra.mapDomainRingHom]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | single h s =>
        simp [MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapRingHom, MonoidAlgebra.mapDomain_single]
  unfold GDet.lam GDet.map GDet.comap GDet.chi
  dsimp only
  rw [MonoidHom.comp_apply]
  erw [key]

/- English proof (translation)
Rewrite using `[← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, h, gDet_lam_map_comap_eq_lam_mapDomainRingHom]`. Both sides reduce to the same expression.
-/
private theorem lam_push {n : ℕ} {R B S H G : Type} [CommRing R] [CommRing B] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n B G} {f : R →+* S} {a : B →+* S} {φ : H →* G}
    (h : E.map f = (D.comap φ).map a) (i : ℕ) (y : MonoidAlgebra R H) :
    f (E.lam i y) = (D.map a).lam i (push f φ y) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, h, gDet_lam_map_comap_eq_lam_mapDomainRingHom]
  rfl

/- English proof (translation)
Introduce `l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hn hAd`. Take `⟨hD, hψ, hs, hU, hy⟩` from `m.π_maps`. Establish `hL : ∀ i y, m.π.toRingHom (W.t.D.lam i y) = (u.D.map (algebraMap B (Spo A))).lam i (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y)` using `fun i y => lam_push hD i y`. Establish `hT : ∀ y, m.π (W.t.D.tr y) = (u.D.map (algebraMap B (Spo A))).tr (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y)` using `fun y => hL 1 y`. Establish `hz : ∀ h y, y ∈ (u.D.map (algebraMap B (Spo A))).toDet.ker → (u.D.map (algebraMap B (Spo A))).tr (h * y) = 0` using `fun h y hy => tr_ker _ hn hy h`.

Establish `hz0 : (u.D.map (algebraMap B (Spo A))).tr 0 = 0`. Simplify using `using hz 1 0 (TwoSidedIdeal.zero_mem _)`. Establish `hmapTr : ∀ x, (u.D.map (algebraMap B (Spo A))).tr (MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) x) = algebraMap B (Spo A) (u.D.tr x)` using `fun x => ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) x).2 1`. Establish `hc : (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))).comp (algebraMap W.R (MonoidAlgebra W.R (Ph0 Λ))) = (algebraMap (Spo A) (MonoidAlgebra (Spo A) G0.frame.G₀)).comp m.π.toRingHom`. Use extensionality with `c`.

Simplify using `[push_single, MonoidAlgebra.coe_algebraMap]`. Rewrite using `[ii, Ideal.span_le]`. Introduce `x hx`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Proceed by induction on `hx`.

Use `next h k hk =>`. Rewrite using `[hT, map_mul, map_sub, map_one, push_single, push_single]`. Simplify using `[hk, ← MonoidAlgebra.one_def, hz0]`. Use `next i g g' hg =>`. Establish `hL' : ∀ i y, m.π (W.t.D.lam i y) = (u.D.map (algebraMap B (Spo A))).lam i (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y)` using `hL`.

Establish `hlam : ∀ z, (u.D.map (algebraMap B (Spo A))).lam i (MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) z) = algebraMap B (Spo A) (u.D.lam i z)` using `fun z => ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) z).2 i`. Establish `heps : ∀ (x : Λ.G.G₀) (k : ℤ), m.π (((Λ.G.frame.eps O W.R x ^ k : W.Rˣ)) : W.R) = (((G0.frame.eps O (Spo A) (Λ.h.p₀ x) ^ k : (Spo A)ˣ)) : Spo A)`. Introduce `x k`. Rewrite using `[Λ.h.eps_p₀]`. Establish `hu : Units.map (m.π : W.R →* Spo A) (Λ.G.frame.eps O W.R x) = Λ.G.frame.eps O (Spo A) x`.

Use `ext`. Simplify using `[GFrame.eps, pushCh]`. Rewrite using `[← hu]`. Conclude with `congrArg Units.val (map_zpow (Units.map (m.π : W.R →* Spo A)) (Λ.G.frame.eps O W.R x) k)`. Establish `hepsB : ∀ (y : G0.G₀) (k : ℤ), algebraMap B (Spo A) (((G0.frame.eps O B y ^ k : Bˣ)) : B) = (((G0.frame.eps O (Spo A) y ^ k : (Spo A)ˣ)) : Spo A)`.

Introduce `y k`. Establish `hu : Units.map (algebraMap B (Spo A) : B →* Spo A) (G0.frame.eps O B y) = G0.frame.eps O (Spo A) y`. Use `ext`. Simplify using `[GFrame.eps, pushCh, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[← hu]`.

Conclude with `congrArg Units.val (map_zpow (Units.map (algebraMap B (Spo A) : B →* Spo A)) (G0.frame.eps O B y) k)`. Establish `hconj : πo0 Λ g' = Λ.G.frame.conj (πo0 Λ g)` using `by clear hL hT hz hz0 hmapTr hs hD hAd hy hU hc hψ hL' hlam heps hepsB`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show Λ.πo (g' : Λ.Ph) = Λ.G.c * Λ.πo (g : Λ.Ph) * Λ.G.c⁻¹`. Rewrite using `[hg, map_mul, map_mul, map_inv, Λ.ct_o]`.

Establish `h1 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (MonoidAlgebra.single g'⁻¹ (((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ)) : W.R)) = MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) (G0.frame.star O B n (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ g)) 1))`. Unfold `GFrame.star GFrame.starOp`. Rewrite using `[MonoidAlgebra.lift_single, one_smul]`. Simplify using `only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]`. Rewrite using `[MonoidAlgebra.mapRingHom_single, push_single]`.

Use `congr 1`. Rewrite using `[map_inv, MonoidHom.comp_apply, hconj, Λ.h.p₀_conj]`. Rewrite using `[hepsB]`. Conclude with `heps _ _`. Establish `h2 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (MonoidAlgebra.single g 1) = MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ g)) 1)`.

Rewrite using `[push_single, MonoidAlgebra.mapRingHom_single, map_one, map_one, MonoidHom.comp_apply]`. Rewrite using `[map_sub, hL', hL', h1, h2, hlam, hlam, u.P, sub_self]`. Use `next v g ga h hga =>`. Establish `hpt : ∀ i, m.π.toRingHom ((W.t.ψ v i (g i) : W.R)) = algebraMap B (Spo A) ((u.ψ v i (g i) : B))`. Introduce `i`.

Use `congrArg (fun χ : L.Gv v →* (Spo A)ˣ => ((χ (g i) : (Spo A)ˣ) : Spo A)) (hψ v i)` as an intermediate fact. Simplify `this` using `[pushCh]`. Establish `hp : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) 1 - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.R))).prod) = MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ h)) 1 * G …` using `by clear hL hT hz hz0 hmapTr hs hD hAd hy hU hc`. Unfold `GFrame.oEl`. Rewrite using `[map_mul, map_mul, push_single, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]`.

Use `congr 1`. Rewrite using `[MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, map_one, map_one]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Establish `hpt' : m.π ((W.t.ψ v i (g i) : W.R)) = algebraMap B (Spo A) ((u.ψ v i (g i) : B))` using `hpt i`.

Rewrite using `[Function.comp_apply, Function.comp_apply, map_sub, map_sub, push_single, push_single, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, hga, Λ.h.p₀_φ, map_one, map_one]`. Conclude with `congrArg (fun c => MonoidAlgebra.single _ 1 - MonoidAlgebra.single 1 c) hpt'`. Rewrite using `[hT, hp, hmapTr, u.Ord, map_zero]`. Use `next w g ga h hg hga =>`. Establish `hp : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)) = MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ h)) 1 * (MonoidAlgebra.single (G0.φu w g) 1 - 1))`.

Simplify using `only [map_mul, map_sub, map_one, push_single, MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, hga, Λ.h.p₀_φu]`. Establish `hmem : G0.φu w g ∈ r.Ip w`. Rewrite using `[hAd.2 w]`. Conclude with `Subgroup.mem_map_of_mem _ hg`. Rewrite using `[hT, hp, hmapTr, u.I w _ hmem, map_zero]`.

Use `next j ph h hph =>`. Establish `hchi : (u.D.map (algebraMap B (Spo A))).chi (MonoidAlgebra.single (T.sg j) 1) = Polynomial.map (algebraMap B (Spo A)) (u.D.chi (MonoidAlgebra.single (T.sg j) 1))`. Use `((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) (MonoidAlgebra.single (T.sg j) 1)).1` as an intermediate fact. Simplify `this` using `[MonoidAlgebra.mapRingHom]`. Establish `hq : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (q1El ph (W.t.U j)) = Polynomial.aeval (MonoidAlgebra.single (T.sg j) (1 : Spo A)) ((u.D.map (algebraMap B (Spo A))).chi (MonoidAlgebra.single (T.sg j) 1))` using `by clear hL hT hz hz0 hmapTr hψ hs hD hAd hy`.

Rewrite using `[charpoly_element_eq_aeval_group_element, Polynomial.aeval_def, Polynomial.hom_eval₂, hc, ← Polynomial.eval₂_map, ← Polynomial.aeval_def, push_single, MonoidHom.comp_apply, hph, Λ.p_ph, map_one, hchi, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Rewrite using `[← (spRoots B T.q n _ _ j).1]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Conclude with `congrArg (fun c => Polynomial.X - Polynomial.C c) (hU j i)`. Rewrite using `[hT, map_mul, push_single, hq]`. Apply `hz` to reduce the goal to its premises. Use `ch_ker (u.D.map (algebraMap B (Spo A))).toDet (MonoidAlgebra.single (T.sg j) 1)` as an intermediate fact. Rewrite `this` using `[(UpperTheory.V.CA.d_toDet _ _).1]`. Then use the resulting hypothesis.

Use `next j i ph ta h hph hta =>`. Establish `h0 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 (W.t.y j i)) = 0`. Rewrite using `[map_sub, map_sub, map_one, push_single, push_single, MonoidHom.comp_apply, hta, Λ.p_ta, map_one, hy, MonoidAlgebra.single_zero, sub_zero, ← MonoidAlgebra.one_def, sub_self]`. Rewrite using `[hT]`. Unfold `q2El`.

Rewrite using `[map_mul, map_mul, h0, mul_zero, mul_zero, hz0]`.
-/
theorem UpperTheory.V.Pa.Core.piKer :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), 1 ≤ n → Adapted T (r := r) → ii W ≤ RingHom.ker m.π := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hn hAd
  obtain ⟨hD, hψ, hs, hU, hy⟩ := m.π_maps
  have hL : ∀ i y, m.π.toRingHom (W.t.D.lam i y) =
      (u.D.map (algebraMap B (Spo A))).lam i (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) :=
    fun i y => lam_push hD i y
  have hT : ∀ y, m.π (W.t.D.tr y) =
      (u.D.map (algebraMap B (Spo A))).tr (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) :=
    fun y => hL 1 y
  have hz : ∀ h y, y ∈ (u.D.map (algebraMap B (Spo A))).toDet.ker →
      (u.D.map (algebraMap B (Spo A))).tr (h * y) = 0 :=
    fun h y hy => tr_ker _ hn hy h
  have hz0 : (u.D.map (algebraMap B (Spo A))).tr 0 = 0 := by
    simpa using hz 1 0 (TwoSidedIdeal.zero_mem _)
  have hmapTr : ∀ x, (u.D.map (algebraMap B (Spo A))).tr
      (MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) x) = algebraMap B (Spo A) (u.D.tr x) :=
    fun x => ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) x).2 1
  have hc : (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))).comp
      (algebraMap W.R (MonoidAlgebra W.R (Ph0 Λ))) =
      (algebraMap (Spo A) (MonoidAlgebra (Spo A) G0.frame.G₀)).comp m.π.toRingHom := by
    ext c
    simp [push_single, MonoidAlgebra.coe_algebraMap]
  rw [ii, Ideal.span_le]
  intro x hx
  rw [SetLike.mem_coe, RingHom.mem_ker]
  induction hx
  next h k hk =>
    rw [hT, map_mul, map_sub, map_one, push_single, push_single]
    simp [hk, ← MonoidAlgebra.one_def, hz0]
  next i g g' hg =>
    have hL' : ∀ i y, m.π (W.t.D.lam i y) =
        (u.D.map (algebraMap B (Spo A))).lam i (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) := hL
    have hlam : ∀ z, (u.D.map (algebraMap B (Spo A))).lam i
        (MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) z) = algebraMap B (Spo A) (u.D.lam i z) :=
      fun z => ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) z).2 i
    have heps : ∀ (x : Λ.G.G₀) (k : ℤ), m.π (((Λ.G.frame.eps O W.R x ^ k : W.Rˣ)) : W.R) =
        (((G0.frame.eps O (Spo A) (Λ.h.p₀ x) ^ k : (Spo A)ˣ)) : Spo A) := by
      intro x k
      rw [Λ.h.eps_p₀]
      have hu : Units.map (m.π : W.R →* Spo A) (Λ.G.frame.eps O W.R x) = Λ.G.frame.eps O (Spo A) x := by
        ext
        simp [GFrame.eps, pushCh]
      rw [← hu]
      exact congrArg Units.val (map_zpow (Units.map (m.π : W.R →* Spo A)) (Λ.G.frame.eps O W.R x) k)
    have hepsB : ∀ (y : G0.G₀) (k : ℤ), algebraMap B (Spo A) (((G0.frame.eps O B y ^ k : Bˣ)) : B) =
        (((G0.frame.eps O (Spo A) y ^ k : (Spo A)ˣ)) : Spo A) := by
      intro y k
      have hu : Units.map (algebraMap B (Spo A) : B →* Spo A) (G0.frame.eps O B y) = G0.frame.eps O (Spo A) y := by
        ext
        simp [GFrame.eps, pushCh, ← IsScalarTower.algebraMap_apply]
      rw [← hu]
      exact congrArg Units.val (map_zpow (Units.map (algebraMap B (Spo A) : B →* Spo A)) (G0.frame.eps O B y) k)
    have hconj : πo0 Λ g' = Λ.G.frame.conj (πo0 Λ g) := by
      clear hL hT hz hz0 hmapTr hs hD hAd hy hU hc hψ hL' hlam heps hepsB
      apply Subtype.ext
      show Λ.πo (g' : Λ.Ph) = Λ.G.c * Λ.πo (g : Λ.Ph) * Λ.G.c⁻¹
      rw [hg, map_mul, map_mul, map_inv, Λ.ct_o]
    have h1 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single g'⁻¹ (((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ)) : W.R)) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (G0.frame.star O B n (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ g)) 1)) := by
      unfold GFrame.star GFrame.starOp
      rw [MonoidAlgebra.lift_single, one_smul]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
      rw [MonoidAlgebra.mapRingHom_single, push_single]
      congr 1
      · rw [map_inv, MonoidHom.comp_apply, hconj, Λ.h.p₀_conj]
      · rw [hepsB]
        exact heps _ _
    have h2 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ g)) 1) := by
      rw [push_single, MonoidAlgebra.mapRingHom_single, map_one, map_one, MonoidHom.comp_apply]
    rw [map_sub, hL', hL', h1, h2, hlam, hlam, u.P, sub_self]
  next v g ga h hga =>
    have hpt : ∀ i, m.π.toRingHom ((W.t.ψ v i (g i) : W.R)) =
        algebraMap B (Spo A) ((u.ψ v i (g i) : B)) := by
      intro i
      have := congrArg (fun χ : L.Gv v →* (Spo A)ˣ => ((χ (g i) : (Spo A)ˣ) : Spo A)) (hψ v i)
      simpa [pushCh] using this
    have hp : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) 1 -
          MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.R))).prod) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ h)) 1 * G0.frame.oEl v (u.ψ v) g) := by
      clear hL hT hz hz0 hmapTr hs hD hAd hy hU hc
      unfold GFrame.oEl
      rw [map_mul, map_mul, push_single, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 1
      · rw [MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, map_one, map_one]
      · congr 2
        funext i
        have hpt' : m.π ((W.t.ψ v i (g i) : W.R)) = algebraMap B (Spo A) ((u.ψ v i (g i) : B)) := hpt i
        rw [Function.comp_apply, Function.comp_apply, map_sub, map_sub, push_single, push_single, MonoidAlgebra.mapRingHom_single,
          MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, hga, Λ.h.p₀_φ, map_one, map_one]
        exact congrArg (fun c => MonoidAlgebra.single _ 1 - MonoidAlgebra.single 1 c) hpt'
    rw [hT, hp, hmapTr, u.Ord, map_zero]
  next w g ga h hg hga =>
    have hp : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ h)) 1 * (MonoidAlgebra.single (G0.φu w g) 1 - 1)) := by
      simp only [map_mul, map_sub, map_one, push_single, MonoidAlgebra.mapRingHom_single,
        MonoidHom.comp_apply, hga, Λ.h.p₀_φu]
    have hmem : G0.φu w g ∈ r.Ip w := by
      rw [hAd.2 w]
      exact Subgroup.mem_map_of_mem _ hg
    rw [hT, hp, hmapTr, u.I w _ hmem, map_zero]
  next j ph h hph =>
    have hchi : (u.D.map (algebraMap B (Spo A))).chi (MonoidAlgebra.single (T.sg j) 1) =
        Polynomial.map (algebraMap B (Spo A)) (u.D.chi (MonoidAlgebra.single (T.sg j) 1)) := by
      have := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A))
        (MonoidAlgebra.single (T.sg j) 1)).1
      simpa [MonoidAlgebra.mapRingHom] using this
    have hq : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (q1El ph (W.t.U j)) =
        Polynomial.aeval (MonoidAlgebra.single (T.sg j) (1 : Spo A))
          ((u.D.map (algebraMap B (Spo A))).chi (MonoidAlgebra.single (T.sg j) 1)) := by
      clear hL hT hz hz0 hmapTr hψ hs hD hAd hy
      rw [charpoly_element_eq_aeval_group_element, Polynomial.aeval_def, Polynomial.hom_eval₂, hc, ← Polynomial.eval₂_map,
        ← Polynomial.aeval_def, push_single, MonoidHom.comp_apply, hph, Λ.p_ph, map_one, hchi,
        Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [← (spRoots B T.q n _ _ j).1]
      congr 2
      funext i
      exact congrArg (fun c => Polynomial.X - Polynomial.C c) (hU j i)
    rw [hT, map_mul, push_single, hq]
    apply hz
    have := ch_ker (u.D.map (algebraMap B (Spo A))).toDet (MonoidAlgebra.single (T.sg j) 1)
    rwa [(UpperTheory.V.CA.d_toDet _ _).1] at this
  next j i ph ta h hph hta =>
    have h0 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 (W.t.y j i)) = 0 := by
      rw [map_sub, map_sub, map_one, push_single, push_single, MonoidHom.comp_apply, hta, Λ.p_ta,
        map_one, hy, MonoidAlgebra.single_zero, sub_zero, ← MonoidAlgebra.one_def, sub_self]
    rw [hT]
    unfold q2El
    rw [map_mul, map_mul, h0, mul_zero, mul_zero, hz0]
