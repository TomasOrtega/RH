import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.ComplOfNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FibreTraces.FibTrdeg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HighestWeightIntegral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KStableHighestWeightVector

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Cu

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `e1` using `congrFun (congrFun h1 1) 0`. Establish `e2` using `congrFun (congrFun h1 2) 0`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, h2, h3] at e1 e2`. Establish `h32 : n 3 2 ∈ E`.

Establish `: n 3 2 = -n 1 0` using `by linear_combination e1`. Rewrite using `[this]`. Conclude with `neg_mem h10`. Establish `h31 : n 3 1 ∈ E`. Establish `: n 3 1 = n 2 0 - n 2 1 * n 1 0` using `by linear_combination -e2`.

Rewrite using `[this]`. Conclude with `sub_mem h20 (mul_mem h21 h10)`. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases. Rewrite using `[h3 i j hij]`. Conclude with `zero_mem _`.

Rewrite using `[h2]`. Conclude with `one_mem _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | assumption | exact absurd hij (by decide)`.
-/
private theorem UpperTheory.V.Cu.FiberPointBoundedGenerators.fib_low {K : Type} [Field K] (E : Subfield K) (n : M4 K) (h : IsLow n) (h10 : n 1 0 ∈ E)
    (h20 : n 2 0 ∈ E) (h30 : n 3 0 ∈ E) (h21 : n 2 1 ∈ E) (i j : Fin 4) : n i j ∈ E := by
  obtain ⟨h1, h2, h3⟩ := h
  have e1 := congrFun (congrFun h1 1) 0
  have e2 := congrFun (congrFun h1 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev, h2, h3] at e1 e2
  have h32 : n 3 2 ∈ E := by
    have : n 3 2 = -n 1 0 := by linear_combination e1
    rw [this]; exact neg_mem h10
  have h31 : n 3 1 ∈ E := by
    have : n 3 1 = n 2 0 - n 2 1 * n 1 0 := by linear_combination -e2
    rw [this]; exact sub_mem h20 (mul_mem h21 h10)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [h3 i j hij]; exact zero_mem _
  · rw [h2]; exact one_mem _
  · fin_cases i <;> fin_cases j <;> first | assumption | exact absurd hij (by decide)

/- English proof (translation)
Use `haveI := Fintype.ofFinite Φ.ι`. Establish `hp` using `X.pair.map y`. Take `⟨s, t, hst⟩` from `hTor (mapRep y X.P.r) Φ.g0 hp.nrm hne hS e1 e2 e3 e4`. Set `u : Φ.ι × Fin 4 → K` to `fun x => y (X.P.n x.1 (![1, 2, 3, 2] x.2) (![0, 0, 0, 1] x.2))`. Use `⟨{s, t} ∪ Finset.univ.image u, ?_, fun E hB hT hE z => ?_⟩` and prove the remaining obligations.

Use `(Finset.card_union_le _ _).trans (add_le_add Finset.card_le_two (Finset.card_image_le.trans ?_))` and prove the remaining obligations. Simplify using `[mul_comm]`. Establish `hc : ∀ g n, (mapRep y X.P.r g).charpoly.coeff n ∈ E` using `fun g n => by`. Establish `: (mapRep y X.P.r g).charpoly.coeff n = y (algebraMap X.B X.A ((X.cp g).coeff n))` using `by show ((X.P.r g).map y).charpoly.coeff n = _`. Rewrite using `[Matrix.charpoly_map, ← X.cp_map, coeff_map, coeff_map]`.

Rewrite using `[this]`. Conclude with `hB _`. Establish `hr` using `hst E (hT _ (by simp)) (hT _ (by simp)) (fun g => by rw [Matrix.trace_eq_neg_charpoly_coeff]; exact neg_mem (hc _ _)) (fun i => hE _ _ (Matrix.charpoly_monic _) (hc Φ.g0) (by`. Establish `hd : mapRep y X.P.r Φ.g0 = Matrix.diagonal fun i => mapRep y X.P.r Φ.g0 i i` using `hp.nrm.diagonal_diag.symm`. Rewrite using `[IsRoot, hd, Matrix.charpoly_diagonal, eval_prod]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simp)))`. Establish `hu : ∀ x, u x ∈ E` using `fun x => hT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))`. Establish `hn` using `fun v => FiberPointBoundedGenerators.fib_low E _ (hp.low v) (hu (v, 0)) (hu (v, 1)) (hu (v, 2)) (hu (v, 3))`. Establish `hz : z ∈ (⊤ : Subalgebra X.B X.A)` using `trivial`. Rewrite `hz` using `[← X.gen]`.

Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem z hz`. Break down `hz with ⟨t, rfl⟩ | ⟨t, rfl⟩` into its components or cases. Conclude with `hr _ _ _`. Conclude with `hn _ _ _`.

Consider the case `algebraMap b => exact hB b`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `mul y z _ _ hy hz => rw [map_mul]`. Conclude with `mul_mem hy hz`.
-/
private theorem UpperTheory.V.Cu.FiberPointBoundedGenerators.fib_gen {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (X : Space Φ a) {K : Type} [Field K] (y : X.A →+* K)
    (hne : ∀ i j, i ≠ j → y (X.P.r Φ.g0 i i) ≠ y (X.P.r Φ.g0 j j)) (hTor : TorusY)
    (hS : Supp yY (mapRep y X.P.r)) (e1 : Ent (mapRep y X.P.r) wBe) (e2 : Ent (mapRep y X.P.r) (-wBe))
    (e3 : Ent (mapRep y X.P.r) wTh) (e4 : Ent (mapRep y X.P.r) (-wTh)) :
    ∃ T : Finset K, T.card ≤ 2 + 4 * Nat.card Φ.ι ∧ ∀ E : Subfield K, (∀ b, y (algebraMap X.B X.A b) ∈ E) → (∀ t ∈ T, t ∈ E) →
      (∀ (p : K[X]) (x : K), p.Monic → (∀ n, p.coeff n ∈ E) → p.IsRoot x → x ∈ E) → ∀ z, y z ∈ E := by
  classical
  haveI := Fintype.ofFinite Φ.ι
  have hp := X.pair.map y
  obtain ⟨s, t, hst⟩ := hTor (mapRep y X.P.r) Φ.g0 hp.nrm hne hS e1 e2 e3 e4
  let u : Φ.ι × Fin 4 → K := fun x => y (X.P.n x.1 (![1, 2, 3, 2] x.2) (![0, 0, 0, 1] x.2))
  refine ⟨{s, t} ∪ Finset.univ.image u, ?_, fun E hB hT hE z => ?_⟩
  · refine (Finset.card_union_le _ _).trans (add_le_add Finset.card_le_two (Finset.card_image_le.trans ?_))
    simp [mul_comm]
  · have hc : ∀ g n, (mapRep y X.P.r g).charpoly.coeff n ∈ E := fun g n => by
      have : (mapRep y X.P.r g).charpoly.coeff n = y (algebraMap X.B X.A ((X.cp g).coeff n)) := by
        show ((X.P.r g).map y).charpoly.coeff n = _
        rw [Matrix.charpoly_map, ← X.cp_map, coeff_map, coeff_map]
      rw [this]; exact hB _
    have hr := hst E (hT _ (by simp)) (hT _ (by simp))
      (fun g => by rw [Matrix.trace_eq_neg_charpoly_coeff]; exact neg_mem (hc _ _))
      (fun i => hE _ _ (Matrix.charpoly_monic _) (hc Φ.g0) (by
        have hd : mapRep y X.P.r Φ.g0 = Matrix.diagonal fun i => mapRep y X.P.r Φ.g0 i i := hp.nrm.diagonal_diag.symm
        rw [IsRoot, hd, Matrix.charpoly_diagonal, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)))
    have hu : ∀ x, u x ∈ E := fun x => hT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
    have hn := fun v => FiberPointBoundedGenerators.fib_low E _ (hp.low v) (hu (v, 0)) (hu (v, 1)) (hu (v, 2)) (hu (v, 3))
    have hz : z ∈ (⊤ : Subalgebra X.B X.A) := trivial
    rw [← X.gen] at hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact hr _ _ _
      · exact hn _ _ _
    | algebraMap b => exact hB b
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

/- English proof (translation)
Introduce `hTor`. Unfold `FibY`. Introduce `O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hΦ X c hc R _ _ _ f hf q hq r hr hS e1 e2 e3 e4`. Substitute `hr` using the available equality. Use `haveI := X.noeth`.

Use `haveI := X.ft`. Use `letI : Algebra X.A R := (f : X.A →+* R).toAlgebra`. Use `haveI : IsScalarTower Λ X.A R := IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm`. Establish `hff : IsScalarTower.toAlgHom Λ X.A R = f` using `AlgHom.ext fun _ => rfl`. Take `⟨hx, hR⟩` from `fibCpl (Λ := Λ) (A := X.A) (R := R) (fun R' _ _ _ g hg => by`.

Rewrite `hg`, the goal using `[hff]`. Take `⟨h, hh, hu⟩` from `hf.2 R' (X.P.map (g : X.A →+* R')) ⟨X.pair_map g, X.cont_map g, by`. Rewrite using `[← hf.1.red]`. Conclude with `congrArg (fun φ : X.A →ₐ[Λ] ResidueField Λ => X.P.map (φ : X.A →+* ResidueField Λ)) hg⟩`. Conclude with `⟨h, X.hom_ext _ _ hh, fun h' e => hu h' (by rw [← e]; rfl)⟩)`.

Establish `hxB : ((maximalIdeal R).comap (algebraMap X.A R)).comap (algebraMap X.B X.A) = maximalIdeal X.B`. Use extensionality with `b`. Use `show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R ↔ _`. Rewrite using `[← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]`. Use `haveI hη : (q.comap (algebraMap X.A R)).IsPrime := Ideal.comap_isPrime _ q`.

Take `⟨t, h1, h2⟩` from `UpperTheory.V.CA.c3b Λ _ (UpperTheory.V.CA.IsCL.of_isCO Λ X.B) hxB (q.comap (algebraMap X.A R)) (Ideal.comap_mono (le_maximalIdeal hq.ne_top))`. Take `⟨T, hT, hE⟩` from `FiberPointBoundedGenerators.fib_gen X _ (fun i j hij e => by`. Establish `e1 : f (X.P.r Φ.g0 i i) - f (X.P.r Φ.g0 j j) ∈ q` using `Ideal.Quotient.eq.1 (IsFractionRing.injective (R ⧸ q) (FractionRing (R ⧸ q)) e)`. Establish `e2` using `(res_eq_zero_iff Λ R _).2 (le_maximalIdeal hq.ne_top e1)`. Establish `e3 : ∀ i, res Λ R (f (X.P.r Φ.g0 i i)) = (residue Λ).comp a (Φ.χ i Φ.g0)` using `fun i => by`.

Rewrite using `[← hc.res.diag, ← hf.1.red]`. Both sides reduce to the same expression. Rewrite `e2` using `[map_sub, e3, e3]`. Conclude with `(hΦ.ok.dist i j hij).ne_zero e2) hTor hS e1 e2 e3 e4`. Establish `h3` using `fibTrdeg (D := X.B ⧸ (q.comap (algebraMap X.A R)).comap (algebraMap X.B X.A)) ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.quotientMap q (algebraMap X.A R) le_rfl)) T (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective (R ⧸ q) _).comp Ideal.quotientMap_injectiv …`.

Take `⟨z, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Conclude with `hE E (fun b => hB (Ideal.Quotient.mk _ b)) hT' hcl z)`. Rewrite `h3` using `[h1]`. Establish `h4 : t ≤ 2 + 4 * Nat.card Φ.ι` using `le_trans (by exact_mod_cast h3) hT`. Use `((UpperTheory.V.CA.c3c _ hR).2 _ q le_rfl).trans ?_` and prove the remaining obligations.

Rewrite using `[h2]`. Conclude with `add_le_add le_rfl (by exact_mod_cast h4)`.
-/
theorem UpperTheory.V.Cu.fibY_of : TorusY → FibY := by
  intro hTor
  unfold FibY
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hΦ X c hc R _ _ _ f hf q hq r hr hS e1 e2 e3 e4
  subst hr
  haveI := X.noeth
  haveI := X.ft
  letI : Algebra X.A R := (f : X.A →+* R).toAlgebra
  haveI : IsScalarTower Λ X.A R := IsScalarTower.of_algebraMap_eq fun z => (f.commutes z).symm
  have hff : IsScalarTower.toAlgHom Λ X.A R = f := AlgHom.ext fun _ => rfl
  obtain ⟨hx, hR⟩ := fibCpl (Λ := Λ) (A := X.A) (R := R) (fun R' _ _ _ g hg => by
    rw [hff] at hg ⊢
    obtain ⟨h, hh, hu⟩ := hf.2 R' (X.P.map (g : X.A →+* R')) ⟨X.pair_map g, X.cont_map g, by
      rw [← hf.1.red]
      exact congrArg (fun φ : X.A →ₐ[Λ] ResidueField Λ => X.P.map (φ : X.A →+* ResidueField Λ)) hg⟩
    exact ⟨h, X.hom_ext _ _ hh, fun h' e => hu h' (by rw [← e]; rfl)⟩)
  have hxB : ((maximalIdeal R).comap (algebraMap X.A R)).comap (algebraMap X.B X.A) = maximalIdeal X.B := by
    ext b
    show (f.comp (IsScalarTower.toAlgHom Λ X.B X.A)) b ∈ maximalIdeal R ↔ _
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
  haveI hη : (q.comap (algebraMap X.A R)).IsPrime := Ideal.comap_isPrime _ q
  obtain ⟨t, h1, h2⟩ := UpperTheory.V.CA.c3b Λ _ (UpperTheory.V.CA.IsCL.of_isCO Λ X.B) hxB (q.comap (algebraMap X.A R))
    (Ideal.comap_mono (le_maximalIdeal hq.ne_top))
  obtain ⟨T, hT, hE⟩ := FiberPointBoundedGenerators.fib_gen X _ (fun i j hij e => by
    have e1 : f (X.P.r Φ.g0 i i) - f (X.P.r Φ.g0 j j) ∈ q :=
      Ideal.Quotient.eq.1 (IsFractionRing.injective (R ⧸ q) (FractionRing (R ⧸ q)) e)
    have e2 := (res_eq_zero_iff Λ R _).2 (le_maximalIdeal hq.ne_top e1)
    have e3 : ∀ i, res Λ R (f (X.P.r Φ.g0 i i)) = (residue Λ).comp a (Φ.χ i Φ.g0) := fun i => by
      rw [← hc.res.diag, ← hf.1.red]; rfl
    rw [map_sub, e3, e3] at e2
    exact (hΦ.ok.dist i j hij).ne_zero e2) hTor hS e1 e2 e3 e4
  have h3 := fibTrdeg (D := X.B ⧸ (q.comap (algebraMap X.A R)).comap (algebraMap X.B X.A))
    ((algebraMap (R ⧸ q) (FractionRing (R ⧸ q))).comp (Ideal.quotientMap q (algebraMap X.A R) le_rfl)) T
    (by rw [RingHom.coe_comp]; exact (IsFractionRing.injective (R ⧸ q) _).comp Ideal.quotientMap_injective) Ideal.quotientMap_injective
    (fun E hB hT' hcl z => by
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact hE E (fun b => hB (Ideal.Quotient.mk _ b)) hT' hcl z)
  rw [h1] at h3
  have h4 : t ≤ 2 + 4 * Nat.card Φ.ι := le_trans (by exact_mod_cast h3) hT
  refine ((UpperTheory.V.CA.c3c _ hR).2 _ q le_rfl).trans ?_
  rw [h2]
  exact add_le_add le_rfl (by exact_mod_cast h4)
