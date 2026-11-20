import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.StarMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.IsProLOfPL
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.PairKills
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GChmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetCH
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem dom_single {R G H : Type} [CommRing R] [Group G] [Group H] (φ : G →* H) (g : G) (a : R) :
    MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) a := by
  simp

/- English proof (translation)
Establish `hadd : ∀ (F : GFrame l) (a b : MonoidAlgebra R F.G₀), F.star O R n (a + b) = F.star O R n a + F.star O R n b`. Introduce `F a b`. Unfold `GFrame.star`. Simplify using the standard rewrite rules. Establish `hsg : ∀ (F : GFrame l) (g : F.G₀) (b : R), F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ↑((F.eps O R) g ^ (1 - (n : ℤ))))`.

Introduce `F g b`. Unfold `GFrame.star GFrame.starOp`. Simplify using `[MonoidAlgebra.lift_single]`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero`.

Unfold `GFrame.star`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb => rw [hadd, map_add, ha, hb, map_add, hadd]`. Consider the case `single g b => rw [hsg, dom_single, dom_single, hsg, map_inv, h.p₀_conj, h.eps_p₀]`.
-/
private theorem star_dom {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (h : G.Hom G') (O R : Type) [CommRing O]
    [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] (n : ℕ) (y : MonoidAlgebra R G.G₀) :
    MonoidAlgebra.mapDomainRingHom R h.p₀ (G.frame.star O R n y) =
      G'.frame.star O R n (MonoidAlgebra.mapDomainRingHom R h.p₀ y) := by
  have hadd : ∀ (F : GFrame l) (a b : MonoidAlgebra R F.G₀),
      F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro F a b
    unfold GFrame.star
    simp
  have hsg : ∀ (F : GFrame l) (g : F.G₀) (b : R), F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ↑((F.eps O R) g ^ (1 - (n : ℤ)))) := by
    intro F g b
    unfold GFrame.star GFrame.starOp
    simp [MonoidAlgebra.lift_single]
  induction y using MonoidAlgebra.induction_linear with
  | zero =>
    unfold GFrame.star
    simp
  | add a b ha hb => rw [hadd, map_add, ha, hb, map_add, hadd]
  | single g b => rw [hsg, dom_single, dom_single, hsg, map_inv, h.p₀_conj, h.eps_p₀]

/- English proof (translation)
Unfold `GFrame.oEl`. Rewrite using `[map_list_prod, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, map_sub, dom_single, map_one]`.

Use `congr 2`. Conclude with `h.p₀_φ v (g i)`.
-/
private theorem oEl_dom {l : ℕ} [Fact l.Prime] {L : Loc} {G G' : Glob l L} (h : G.Hom G') {R : Type}
    [CommRing R] {n : ℕ} (v : L.Vl) (ψ : Fin n → L.Gv v →* Rˣ) (g : Fin n → L.Gv v) :
    MonoidAlgebra.mapDomainRingHom R h.p₀ (G.frame.oEl v ψ g) = G'.frame.oEl v ψ g := by
  unfold GFrame.oEl
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp only [Function.comp_apply, map_sub, dom_single, map_one]
  congr 2
  exact h.p₀_φ v (g i)

/- English proof (translation)
Unfold `q1El`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, map_mul, ih (fun i => u i.succ)]`.

Use `congr 1`. Simplify using `[MonoidAlgebra.coe_algebraMap]`.
-/
private theorem charpoly_element_eq_aeval_group_element {R G : Type} [CommRing R] [Group G] {n : ℕ} (g : G) (u : Fin n → R) :
    q1El g u = Polynomial.aeval (MonoidAlgebra.single g (1 : R)) (∏ i, (Polynomial.X - Polynomial.C (u i))) := by
  unfold q1El
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, map_mul, ih (fun i => u i.succ)]
    congr 1
    simp [MonoidAlgebra.coe_algebraMap]

/- English proof (translation)
Rewrite using `[Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]`. Use `congr 1`. Use extensionality with `r`. Simplify using `[MonoidAlgebra.mapRingHom]`. Simplify using `[MonoidAlgebra.mapRingHom]`.
-/
private theorem aeval_push {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (g : G)
    (P : Polynomial R) : MonoidAlgebra.mapRingHom G f (Polynomial.aeval (MonoidAlgebra.single g (1 : R)) P) =
      Polynomial.aeval (MonoidAlgebra.single g (1 : S)) (P.map f) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  · ext r
    simp [MonoidAlgebra.mapRingHom]
  · simp [MonoidAlgebra.mapRingHom]

/- English proof (translation)
Unfold `GDet.chBar closureIdeal`. Use `le_iInf fun N => le_iInf fun H => TwoSidedIdeal.span_mono ?_` and prove the remaining obligations. Conclude with `Set.subset_union_left.trans Set.subset_union_left`.
-/
private theorem le_chBar {n : ℕ} {A G : Type} [CommRing A] [Group G] [IsLocalRing A] [TopologicalSpace G]
    (D : GDet n A G) (Z : Set (MonoidAlgebra A G)) : TwoSidedIdeal.span (D.CH ∪ Z) ≤ D.chBar Z := by
  unfold GDet.chBar closureIdeal
  refine le_iInf fun N => le_iInf fun H => TwoSidedIdeal.span_mono ?_
  exact Set.subset_union_left.trans Set.subset_union_left

/- English proof (translation)
Introduce `l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ o πb hπb hPL hAd hn z hz`. Use `haveI := IsCoef.complete (l := l) (O := O)`. Use `haveI := IsCoef.finite (l := l) (O := O)`. Use `haveI := IsCoef.char (l := l) (O := O)`. Take `⟨-, -, hstarCH, -, -⟩` from `UpperTheory.V.CA.pair_kills r u (BC.phi0 l L G0 T hPL) hn`.

Establish `hmaps` using `ooMaps l L G0 T Λ n O r B u J D A W m o πb hπb`. Take `⟨-, -, -, hU, hy⟩` from `m.π_maps`. Establish `hsm1` using `BC.star_map l Λ.G.frame O O (W.R ⧸ ii W) (Spo A) πb.toRingHom (fun a => πb.commutes _)`. Establish `hsm2` using `BC.star_map l G0.frame O O B (Spo A) (algebraMap B (Spo A)) (fun a => (IsScalarTower.algebraMap_apply O B (Spo A) _).symm)`. Establish `hΦstar : ∀ x : MonoidAlgebra (W.R ⧸ ii W) Λ.G.G₀, MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (Λ.G.frame.star O (W.R ⧸ ii W) n x)) = G0.frame.star O (Spo A) n (MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom …`.

Introduce `x`. Rewrite using `[hsm1.2.1, star_dom]`. Establish `halg : ∀ x : MonoidAlgebra B G0.G₀, MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (G0.frame.star O B n x) = G0.frame.star O (Spo A) n (MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) x)` using `hsm2.2.1 n`. Establish `hmem : ∀ c ∈ augmentationIdealKernel u, MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) c ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) '' augmentationIdealKernel u)` using `fun c hc => TwoSidedIdeal.subset_span ⟨c, hc, rfl⟩`. Establish `hCH : ∀ c ∈ TwoSidedIdeal.span u.D.CH, c ∈ augmentationIdealKernel u` using `fun c hc => le_chBar u.D (pairGens u) (TwoSidedIdeal.span_mono Set.subset_union_left hc)`.

Establish `hPG : ∀ c ∈ pairGens u, c ∈ augmentationIdealKernel u` using `fun c hc => le_chBar u.D (pairGens u) (TwoSidedIdeal.subset_span (Set.subset_union_right hc))`. Establish `hCHq : ∀ j, Polynomial.aeval (MonoidAlgebra.single (T.sg j) (1 : B)) (u.D.chi (MonoidAlgebra.single (T.sg j) 1)) ∈ TwoSidedIdeal.span u.D.CH`. Introduce `j`. Rewrite using `[← UpperTheory.V.CA.d_toDet_CH, ← (UpperTheory.V.CA.d_toDet u.D _).1]`. Conclude with `UpperTheory.V.CA.k_mem _ _`.

Establish `hq1 : ∀ j, MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (q1El (Λ.ph j) (fun i => Ideal.Quotient.mk (ii W) (W.t.U j i)))) = MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (Polynomial.aeval (MonoidAlgebra.single (T.sg j) (1 : B) …`. Introduce `j`. Establish `e1 : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (q1El (Λ.ph j) (fun i => Ideal.Quotient.mk (ii W) (W.t.U j i)))) = q1El (T.sg j) (fun i => Sp.u (fun j ↦ u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i ↦ (algebraMap O B) (A.ut j …`. Unfold `q1El`. Rewrite using `[map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Use `clear hz hmaps hstarCH hsm1 hsm2 hΦstar halg hmem hCH hPG hCHq hy`. Establish `hU' : m.π (W.t.U j i) = Sp.u (fun j ↦ u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i ↦ (algebraMap O B) (A.ut j i)) j i` using `hU j i`. Establish `hms : ∀ (g : Λ.G.G₀) (a : W.R ⧸ ii W), MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (MonoidAlgebra.single g a) = MonoidAlgebra.single g (πb a)` using `fun g a => by`.

Simplify using `[MonoidAlgebra.mapRingHom]`. Simplify using `only [Function.comp_apply, map_sub, hms, dom_single, map_one, hπb, hU', Λ.p_ph]`. Rewrite using `[e1, charpoly_element_eq_aeval_group_element, (spRoots B T.q n _ _ j).1, ← aeval_push]`. Establish `hq2 : ∀ j i, MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (q2El (Λ.ph j) (Λ.ta j) (fun i => Ideal.Quotient.mk (ii W) (W.t.U j i)) i (Ideal.Quotient.mk (ii W) (W.t.y j i)))) = 0`. Introduce `j i`.

Unfold `q2El`. Rewrite using `[map_mul, map_mul]`. Apply `mul_eq_zero_of_right` to reduce the goal to its premises. Use `clear hz hmaps hstarCH hsm1 hsm2 hΦstar halg hmem hCH hPG hCHq hU hq1`. Establish `hy' : m.π (W.t.y j i) = 0` using `hy j i`.

Establish `hms : ∀ (g : Λ.G.G₀) (a : W.R ⧸ ii W), MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (MonoidAlgebra.single g a) = MonoidAlgebra.single g (πb a)` using `fun g a => by`. Simplify using `[MonoidAlgebra.mapRingHom]`. Simplify using `only [map_sub, hms, dom_single, map_one, hπb, hy', Λ.p_ta]`. Simplify using the standard rewrite rules. Rewrite using `[sub_eq_zero]`.

Conclude with `MonoidAlgebra.one_def.symm`. Establish `hstar0 : G0.frame.star O (Spo A) n 0 = 0`. Unfold `GFrame.star`. Simplify using the standard rewrite rules. Unfold `pairGens qGens at hz`.

Simplify using `only [Set.mem_union, Set.mem_setOf_eq] at hz`. Break down `hz with ((⟨v, g, rfl | rfl⟩ | ⟨w, g, hg, rfl | rfl⟩) | (⟨j, rfl | rfl⟩ | ⟨j, i, rfl | rfl⟩))` into its components or cases. Establish `eo : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (Λ.G.frame.oEl v (o.p.ψ v) g)) = MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (G0.frame.oEl v (u.ψ v) g)`. Rewrite using `[hsm1.2.2, oEl_dom, hsm2.2.2]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `hmaps.2 v i`. Rewrite using `[eo]`. Conclude with `hmem _ (hPG _ (by unfold pairGens; exact Or.inl ⟨v, g, Or.inl rfl⟩))`. Establish `eo : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (Λ.G.frame.oEl v (o.p.ψ v) g)) = MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (G0.frame.oEl v (u.ψ v) g)`.

Rewrite using `[hsm1.2.2, oEl_dom, hsm2.2.2]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hmaps.2 v i`. Rewrite using `[hΦstar, eo, ← halg]`.

Conclude with `hmem _ (hPG _ (by unfold pairGens; exact Or.inl ⟨v, g, Or.inr rfl⟩))`. Establish `hg' : Λ.h.p₀ g ∈ r.Ip w`. Unfold `Resid.Ip at hg ⊢`. Rewrite `hg`, the goal using `[Subgroup.mem_inf, Subgroup.mem_iInf]`. Take `⟨hIu, hch⟩` from `hg`.

Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `hIu`. Conclude with `⟨x, hx, (Λ.h.p₀_φu w x).symm⟩`. Establish `hc` using `hch i`. Rewrite `hc` using `[MonoidHom.mem_ker, o.compat.1 i, MonoidHom.comp_apply]`.

Conclude with `hc`. Establish `hms : ∀ (g : Λ.G.G₀) (a : W.R ⧸ ii W), MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (MonoidAlgebra.single g a) = MonoidAlgebra.single g (πb a)` using `fun g a => by`. Simplify using `[MonoidAlgebra.mapRingHom]`. Establish `hma : ∀ (g : G0.G₀) (a : B), MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (MonoidAlgebra.single g a) = MonoidAlgebra.single g (algebraMap B (Spo A) a)` using `fun g a => by`. Simplify using `[MonoidAlgebra.mapRingHom]`.

Establish `e : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (MonoidAlgebra.single g 1 - 1)) = MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (MonoidAlgebra.single (Λ.h.p₀ g) 1 - 1)`. Rewrite using `[map_sub, map_sub, map_one, map_one, hms, dom_single, map_sub, map_one, hma, map_one, map_one]`. Rewrite using `[e]`. Conclude with `hmem _ (hPG _ (by unfold pairGens; exact Or.inr ⟨w, Λ.h.p₀ g, hg', Or.inl rfl⟩))`. Establish `hg' : Λ.h.p₀ g ∈ r.Ip w`.

Unfold `Resid.Ip at hg ⊢`. Rewrite `hg`, the goal using `[Subgroup.mem_inf, Subgroup.mem_iInf]`. Take `⟨hIu, hch⟩` from `hg`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `hIu`.

Conclude with `⟨x, hx, (Λ.h.p₀_φu w x).symm⟩`. Establish `hc` using `hch i`. Rewrite `hc` using `[MonoidHom.mem_ker, o.compat.1 i, MonoidHom.comp_apply]`. Conclude with `hc`. Establish `hms : ∀ (g : Λ.G.G₀) (a : W.R ⧸ ii W), MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (MonoidAlgebra.single g a) = MonoidAlgebra.single g (πb a)` using `fun g a => by`.

Simplify using `[MonoidAlgebra.mapRingHom]`. Establish `hma : ∀ (g : G0.G₀) (a : B), MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (MonoidAlgebra.single g a) = MonoidAlgebra.single g (algebraMap B (Spo A) a)` using `fun g a => by`. Simplify using `[MonoidAlgebra.mapRingHom]`. Establish `e : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (Λ.G.frame.star O (W.R ⧸ ii W) n (MonoidAlgebra.single g 1) - 1)) = MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (G0.frame.star O B n (MonoidAlgebra.single (Λ.h.p₀ g) 1) - 1)`. Rewrite using `[map_sub, map_sub, map_one, map_one, hΦstar, hms, dom_single, map_sub, map_one, halg, hma, map_one, map_one]`.

Rewrite using `[e]`. Conclude with `hmem _ (hPG _ (by unfold pairGens; exact Or.inr ⟨w, Λ.h.p₀ g, hg', Or.inr rfl⟩))`. Rewrite using `[hq1]`. Conclude with `hmem _ (hCH _ (hCHq j))`. Rewrite using `[hΦstar, hq1, ← halg]`.

Conclude with `hmem _ (hCH _ (hstarCH _ (hCHq j)))`. Rewrite using `[hq2]`. Conclude with `TwoSidedIdeal.zero_mem _`. Rewrite using `[hΦstar, hq2, hstar0]`. Conclude with `TwoSidedIdeal.zero_mem _`.
-/
theorem UpperTheory.V.Pa.Core.gensImg :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) [IsCO O (W.R ⧸ ii W)] (o : OoPair W) (πb : (W.R ⧸ ii W) →ₐ[O] Spo A), (∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a) → T.ProL → Adapted T (r := r) → 1 ≤ n → ∀ z ∈ pairGens o.p ∪ qGens (O := O) (F := Λ.G.frame) Λ.ph Λ.ta (fun j i => Ideal.Quotient.mk (ii W) (W.t.U j i)) (fun j i => Ideal.Quotient.mk (ii W) (W.t.y j i)), MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀ (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom z) ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) '' augmentationIdealKernel u) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ o πb hπb hPL hAd hn z hz
  haveI := IsCoef.complete (l := l) (O := O)
  haveI := IsCoef.finite (l := l) (O := O)
  haveI := IsCoef.char (l := l) (O := O)
  obtain ⟨-, -, hstarCH, -, -⟩ := UpperTheory.V.CA.pair_kills r u (BC.phi0 l L G0 T hPL) hn
  have hmaps := ooMaps l L G0 T Λ n O r B u J D A W m o πb hπb
  obtain ⟨-, -, -, hU, hy⟩ := m.π_maps
  have hsm1 := BC.star_map l Λ.G.frame O O (W.R ⧸ ii W) (Spo A) πb.toRingHom
    (fun a => πb.commutes _)
  have hsm2 := BC.star_map l G0.frame O O B (Spo A) (algebraMap B (Spo A))
    (fun a => (IsScalarTower.algebraMap_apply O B (Spo A) _).symm)
  have hΦstar : ∀ x : MonoidAlgebra (W.R ⧸ ii W) Λ.G.G₀,
      MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
        (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (Λ.G.frame.star O (W.R ⧸ ii W) n x)) =
      G0.frame.star O (Spo A) n (MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
        (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom x)) := by
    intro x
    rw [hsm1.2.1, star_dom]
  have halg : ∀ x : MonoidAlgebra B G0.G₀,
      MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (G0.frame.star O B n x) =
      G0.frame.star O (Spo A) n (MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) x) :=
    hsm2.2.1 n
  have hmem : ∀ c ∈ augmentationIdealKernel u, MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) c ∈
      TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) '' augmentationIdealKernel u) :=
    fun c hc => TwoSidedIdeal.subset_span ⟨c, hc, rfl⟩
  have hCH : ∀ c ∈ TwoSidedIdeal.span u.D.CH, c ∈ augmentationIdealKernel u :=
    fun c hc => le_chBar u.D (pairGens u) (TwoSidedIdeal.span_mono Set.subset_union_left hc)
  have hPG : ∀ c ∈ pairGens u, c ∈ augmentationIdealKernel u :=
    fun c hc => le_chBar u.D (pairGens u) (TwoSidedIdeal.subset_span (Set.subset_union_right hc))
  have hCHq : ∀ j, Polynomial.aeval (MonoidAlgebra.single (T.sg j) (1 : B))
      (u.D.chi (MonoidAlgebra.single (T.sg j) 1)) ∈ TwoSidedIdeal.span u.D.CH := by
    intro j
    rw [← UpperTheory.V.CA.d_toDet_CH, ← (UpperTheory.V.CA.d_toDet u.D _).1]
    exact UpperTheory.V.CA.k_mem _ _
  have hq1 : ∀ j, MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
      (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom
        (q1El (Λ.ph j) (fun i => Ideal.Quotient.mk (ii W) (W.t.U j i)))) =
      MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A))
        (Polynomial.aeval (MonoidAlgebra.single (T.sg j) (1 : B))
          (u.D.chi (MonoidAlgebra.single (T.sg j) 1))) := by
    intro j
    have e1 : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
        (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom
          (q1El (Λ.ph j) (fun i => Ideal.Quotient.mk (ii W) (W.t.U j i)))) =
        q1El (T.sg j) (fun i => Sp.u (fun j ↦ u.D.chi (MonoidAlgebra.single (T.sg j) 1))
          (fun j i ↦ (algebraMap O B) (A.ut j i)) j i) := by
      unfold q1El
      rw [map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 2
      funext i
      clear hz hmaps hstarCH hsm1 hsm2 hΦstar halg hmem hCH hPG hCHq hy
      have hU' : m.π (W.t.U j i) = Sp.u (fun j ↦ u.D.chi (MonoidAlgebra.single (T.sg j) 1))
          (fun j i ↦ (algebraMap O B) (A.ut j i)) j i := hU j i
      have hms : ∀ (g : Λ.G.G₀) (a : W.R ⧸ ii W), MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom
          (MonoidAlgebra.single g a) = MonoidAlgebra.single g (πb a) := fun g a => by
        simp [MonoidAlgebra.mapRingHom]
      simp only [Function.comp_apply, map_sub, hms, dom_single, map_one, hπb, hU', Λ.p_ph]
    rw [e1, charpoly_element_eq_aeval_group_element, (spRoots B T.q n _ _ j).1, ← aeval_push]
  have hq2 : ∀ j i, MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
      (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom
        (q2El (Λ.ph j) (Λ.ta j) (fun i => Ideal.Quotient.mk (ii W) (W.t.U j i)) i
          (Ideal.Quotient.mk (ii W) (W.t.y j i)))) = 0 := by
    intro j i
    unfold q2El
    rw [map_mul, map_mul]
    apply mul_eq_zero_of_right
    clear hz hmaps hstarCH hsm1 hsm2 hΦstar halg hmem hCH hPG hCHq hU hq1
    have hy' : m.π (W.t.y j i) = 0 := hy j i
    have hms : ∀ (g : Λ.G.G₀) (a : W.R ⧸ ii W), MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom
        (MonoidAlgebra.single g a) = MonoidAlgebra.single g (πb a) := fun g a => by
      simp [MonoidAlgebra.mapRingHom]
    simp only [map_sub, hms, dom_single, map_one, hπb, hy', Λ.p_ta]
    simp
    rw [sub_eq_zero]
    exact MonoidAlgebra.one_def.symm
  have hstar0 : G0.frame.star O (Spo A) n 0 = 0 := by
    unfold GFrame.star
    simp
  unfold pairGens qGens at hz
  simp only [Set.mem_union, Set.mem_setOf_eq] at hz
  rcases hz with ((⟨v, g, rfl | rfl⟩ | ⟨w, g, hg, rfl | rfl⟩) | (⟨j, rfl | rfl⟩ | ⟨j, i, rfl | rfl⟩))
  · have eo : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
        (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (Λ.G.frame.oEl v (o.p.ψ v) g)) =
        MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (G0.frame.oEl v (u.ψ v) g) := by
      rw [hsm1.2.2, oEl_dom, hsm2.2.2]
      congr 1
      funext i
      exact hmaps.2 v i
    rw [eo]
    exact hmem _ (hPG _ (by unfold pairGens; exact Or.inl ⟨v, g, Or.inl rfl⟩))
  · have eo : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
        (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (Λ.G.frame.oEl v (o.p.ψ v) g)) =
        MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (G0.frame.oEl v (u.ψ v) g) := by
      rw [hsm1.2.2, oEl_dom, hsm2.2.2]
      congr 1
      funext i
      exact hmaps.2 v i
    rw [hΦstar, eo, ← halg]
    exact hmem _ (hPG _ (by unfold pairGens; exact Or.inl ⟨v, g, Or.inr rfl⟩))
  · have hg' : Λ.h.p₀ g ∈ r.Ip w := by
      unfold Resid.Ip at hg ⊢
      rw [Subgroup.mem_inf, Subgroup.mem_iInf] at hg ⊢
      obtain ⟨hIu, hch⟩ := hg
      refine ⟨?_, fun i => ?_⟩
      · obtain ⟨x, hx, rfl⟩ := hIu
        exact ⟨x, hx, (Λ.h.p₀_φu w x).symm⟩
      · have hc := hch i
        rw [MonoidHom.mem_ker, o.compat.1 i, MonoidHom.comp_apply] at hc
        exact hc
    have hms : ∀ (g : Λ.G.G₀) (a : W.R ⧸ ii W), MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom
        (MonoidAlgebra.single g a) = MonoidAlgebra.single g (πb a) := fun g a => by
      simp [MonoidAlgebra.mapRingHom]
    have hma : ∀ (g : G0.G₀) (a : B), MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A))
        (MonoidAlgebra.single g a) = MonoidAlgebra.single g (algebraMap B (Spo A) a) := fun g a => by
      simp [MonoidAlgebra.mapRingHom]
    have e : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
        (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom (MonoidAlgebra.single g 1 - 1)) =
        MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A)) (MonoidAlgebra.single (Λ.h.p₀ g) 1 - 1) := by
      rw [map_sub, map_sub, map_one, map_one, hms, dom_single, map_sub, map_one, hma, map_one, map_one]
    rw [e]
    exact hmem _ (hPG _ (by unfold pairGens; exact Or.inr ⟨w, Λ.h.p₀ g, hg', Or.inl rfl⟩))
  · have hg' : Λ.h.p₀ g ∈ r.Ip w := by
      unfold Resid.Ip at hg ⊢
      rw [Subgroup.mem_inf, Subgroup.mem_iInf] at hg ⊢
      obtain ⟨hIu, hch⟩ := hg
      refine ⟨?_, fun i => ?_⟩
      · obtain ⟨x, hx, rfl⟩ := hIu
        exact ⟨x, hx, (Λ.h.p₀_φu w x).symm⟩
      · have hc := hch i
        rw [MonoidHom.mem_ker, o.compat.1 i, MonoidHom.comp_apply] at hc
        exact hc
    have hms : ∀ (g : Λ.G.G₀) (a : W.R ⧸ ii W), MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom
        (MonoidAlgebra.single g a) = MonoidAlgebra.single g (πb a) := fun g a => by
      simp [MonoidAlgebra.mapRingHom]
    have hma : ∀ (g : G0.G₀) (a : B), MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A))
        (MonoidAlgebra.single g a) = MonoidAlgebra.single g (algebraMap B (Spo A) a) := fun g a => by
      simp [MonoidAlgebra.mapRingHom]
    have e : MonoidAlgebra.mapDomainRingHom (Spo A) Λ.h.p₀
        (MonoidAlgebra.mapRingHom Λ.G.G₀ πb.toRingHom
          (Λ.G.frame.star O (W.R ⧸ ii W) n (MonoidAlgebra.single g 1) - 1)) =
        MonoidAlgebra.mapRingHom G0.G₀ (algebraMap B (Spo A))
          (G0.frame.star O B n (MonoidAlgebra.single (Λ.h.p₀ g) 1) - 1) := by
      rw [map_sub, map_sub, map_one, map_one, hΦstar, hms, dom_single, map_sub, map_one, halg, hma,
        map_one, map_one]
    rw [e]
    exact hmem _ (hPG _ (by unfold pairGens; exact Or.inr ⟨w, Λ.h.p₀ g, hg', Or.inr rfl⟩))
  · rw [hq1]
    exact hmem _ (hCH _ (hCHq j))
  · rw [hΦstar, hq1, ← halg]
    exact hmem _ (hCH _ (hstarCH _ (hCHq j)))
  · rw [hq2]
    exact TwoSidedIdeal.zero_mem _
  · rw [hΦstar, hq2, hstar0]
    exact TwoSidedIdeal.zero_mem _
