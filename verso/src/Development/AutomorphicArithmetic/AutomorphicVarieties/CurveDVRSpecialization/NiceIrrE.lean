import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IrrNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TwoDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

private def IsBlockDiagFinThree {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A) : Prop :=
  M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> rfl`.
-/
private lemma submatrix_corners_three {A : Type} (M : Matrix (Fin 3) (Fin 3) A) :
    M.submatrix ![0, 2] ![0, 2] = !![M 0 0, M 0 2; M 2 0, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `h`. Simplify using `only [submatrix_corners_three, Matrix.charpoly, det_fin_three, det_fin_two]`. Simplify using `[charmatrix_apply, h1, h2, h3, h4]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma charpoly_block_three {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A) (h : IsBlockDiagFinThree M) :
    M.charpoly = (X - C (M 1 1)) * (M.submatrix ![0, 2] ![0, 2]).charpoly := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [submatrix_corners_three, Matrix.charpoly, det_fin_three, det_fin_two]
  simp [charmatrix_apply, h1, h2, h3, h4]
  ring

private def corner {G A : Type} [Group G] [CommRing A] (m : G →* Matrix (Fin 3) (Fin 3) A) (h : ∀ g, IsBlockDiagFinThree (m g)) :
    G →* Matrix (Fin 2) (Fin 2) A where
  toFun g := (m g).submatrix ![0, 2] ![0, 2]
  map_one' := by
    rw [submatrix_corners_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g g' := by
    obtain ⟨h1, h2, h3, h4⟩ := h g
    rw [submatrix_corners_three, submatrix_corners_three, submatrix_corners_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h4]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `choose g hg using hc`. Establish `h0` using `congrFun (congrFun (ho g) 1) 1`. Take `⟨a1, a2, a3, a4⟩` from `h (g 0)`.

Take `⟨b1, b2, b3, b4⟩` from `h (g 2)`. Simplify using `[ordProd, List.ofFn_succ, Matrix.mul_apply, Fin.sum_univ_three, a2, a3, b1, b4, sub_eq_zero] at h0`. Break down `h0 with h0 | h0 | h0` into its components or cases. Conclude with `hg 0 h0`. Conclude with `hg 1 h0`.

Conclude with `hg 2 h0`.
-/
private lemma mid_eq {D κ : Type} [Field κ] (m : D → Matrix (Fin 3) (Fin 3) κ) (h : ∀ g, IsBlockDiagFinThree (m g))
    (ψ : Fin 3 → D → κ) (ho : ∀ g, ordProd m ψ g = 0) : ∃ i, ∀ g, m g 1 1 = ψ i g := by
  by_contra hc
  push Not at hc
  choose g hg using hc
  have h0 := congrFun (congrFun (ho g) 1) 1
  obtain ⟨a1, a2, a3, a4⟩ := h (g 0)
  obtain ⟨b1, b2, b3, b4⟩ := h (g 2)
  simp [ordProd, List.ofFn_succ, Matrix.mul_apply, Fin.sum_univ_three, a2, a3, b1, b4, sub_eq_zero] at h0
  rcases h0 with h0 | h0 | h0
  · exact hg 0 h0
  · exact hg 1 h0
  · exact hg 2 h0

/- English proof (translation)
Establish `hb : ∀ g, IsBlockDiagFinThree ((m g).map φ)` using `fun g => by`. Take `⟨h1, h2, h3, h4⟩` from `h g`. Simplify using `[IsBlockDiagFinThree, h1, h2, h3, h4]`. Take `⟨i, hi⟩` from `mid_eq _ (fun s => hb (ι s)) _ ho`. Set `σ : G →* GL (Fin 2) κ` to `(corner ((φ.mapMatrix : Matrix (Fin 3) (Fin 3) A →+* _).toMonoidHom.comp m) hb).toHomUnits`.

Establish `hσ : gm σ = fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2]` using `rfl`. Rewrite `hirr`, the goal using `[← hσ]`. Use `irrNormal G κ k A 2 Nat.prime_two σ hirr φ red χ hφ (fun g => ?_) D ι (fun a => ψ (i.succAbove a)) (fun g => ?_) U (fun a b hab => ?_) ?_` and prove the remaining obligations. Use `⟨((m g).submatrix ![0, 2] ![0, 2]).charpoly, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.charpoly_map]`.

Both sides reduce to the same expression. Rewrite using `[← Matrix.charpoly_map]`. Simplify using `only [submatrix_corners_three, Matrix.charpoly, det_fin_two, chPoly, Fin.prod_univ_two]`. Simplify using `[charmatrix_apply, h0, h2, mul_eq_zero.1 (h02 g)]`. Establish `e` using `hch g`.

Rewrite `e` using `[charpoly_block_three _ (hb _), hi, chPoly, Fin.prod_univ_succAbove _ i]`. Conclude with `mul_left_cancel₀ (X_sub_C_ne_zero _) e`. Take `⟨g, hg, hg'⟩` from `hs`. Conclude with `⟨g, hg, hg' _ _ fun e => hab (Fin.succAbove_right_injective e)⟩`. Take `⟨g, hg⟩` from `hχ`.

Conclude with `⟨0, 1, g, hg⟩`.
-/
private lemma core {G D κ k A : Type} [Group G] [Group D] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
    (m : G →* Matrix (Fin 3) (Fin 3) A) (h : ∀ g, IsBlockDiagFinThree (m g)) (φ : A →+* κ) (hφ : Function.Injective φ)
    (hirr : MatIrr (⊤ : Subgroup G) fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2])
    (red : A →+* k) (χ : Fin 2 → G →* kˣ) (h0 : ∀ g, red (m g 0 0) = χ 0 g) (h2 : ∀ g, red (m g 2 2) = χ 1 g)
    (h02 : ∀ g, red (m g 0 2) * red (m g 2 0) = 0) (ι : D →* G) (ψ : Fin 3 → D →* κˣ)
    (hch : ∀ g, ((m (ι g)).map φ).charpoly = chPoly ψ g)
    (ho : ∀ g, ordProd (fun s => (m (ι s)).map φ) (fun i s => (ψ i s : κ)) g = 0)
    (U : Subgroup G) [U.Normal] (hs : ∃ g, ι g ∈ U ∧ ∀ a b, a ≠ b → ψ a g ≠ ψ b g)
    (hχ : ∃ g, χ 0 (ι g) ≠ χ 1 (ι g)) :
    MatIrr U fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2] := by
  have hb : ∀ g, IsBlockDiagFinThree ((m g).map φ) := fun g => by
    obtain ⟨h1, h2, h3, h4⟩ := h g
    simp [IsBlockDiagFinThree, h1, h2, h3, h4]
  obtain ⟨i, hi⟩ := mid_eq _ (fun s => hb (ι s)) _ ho
  let σ : G →* GL (Fin 2) κ := (corner ((φ.mapMatrix : Matrix (Fin 3) (Fin 3) A →+* _).toMonoidHom.comp m) hb).toHomUnits
  have hσ : gm σ = fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2] := rfl
  rw [← hσ] at hirr ⊢
  refine irrNormal G κ k A 2 Nat.prime_two σ hirr φ red χ hφ (fun g => ?_) D ι (fun a => ψ (i.succAbove a))
    (fun g => ?_) U (fun a b hab => ?_) ?_
  · refine ⟨((m g).submatrix ![0, 2] ![0, 2]).charpoly, ?_, ?_⟩
    · rw [← Matrix.charpoly_map]; rfl
    · rw [← Matrix.charpoly_map]
      simp only [submatrix_corners_three, Matrix.charpoly, det_fin_two, chPoly, Fin.prod_univ_two]
      simp [charmatrix_apply, h0, h2, mul_eq_zero.1 (h02 g)]
  · have e := hch g
    rw [charpoly_block_three _ (hb _), hi, chPoly, Fin.prod_univ_succAbove _ i] at e
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) e
  · obtain ⟨g, hg, hg'⟩ := hs
    exact ⟨g, hg, hg' _ _ fun e => hab (Fin.succAbove_right_injective e)⟩
  · obtain ⟨g, hg⟩ := hχ
    exact ⟨0, 1, g, hg⟩

end UpperTheory.V.Pr

open Matrix Polynomial IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Pr in
/- English proof (translation)
Introduce `l _ O _ _ _ _ _ F T x L y j hj hN hρ hψ hE U hU`. Establish `hj' : IsLocalHom (j : L.R →+* y.A)` using `⟨hj.map_nonunit⟩`. Take `⟨-, hbar, hid, htri⟩` from `loc_rho T.ok T.n23 T.S x L`. Establish `hO : IsLocalHom (algebraMap O L.R)`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hna`. Establish `h1` using `ha.map j`. Rewrite `h1` using `[AlgHom.commutes, PowerSeries.isUnit_iff_constantCoeff]`. Establish `h2 : residue O a = 0` using `(residue_eq_zero_iff a).2 hna`. Establish `h3 : PowerSeries.constantCoeff (algebraMap O y.A a) = algebraMap (ResidueField O) y.K (residue O a)`.

Rewrite using `[PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, IsScalarTower.algebraMap_apply O (ResidueField O) y.K]`. Both sides reduce to the same expression. Rewrite `h1` using `[h3, h2, map_zero]`. Conclude with `not_isUnit_zero h1`. Establish `hb` using `(hbar (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _).1`.

Use `set φ : y.A →+* y.Fb := (algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr) with hφ`. Establish `hφi : Function.Injective φ` using `(algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)`. Use `set ρ := L.ρ.map (j : L.R →+* y.A) with hρd`. Use `set f : T.S.A →+* y.Fb := φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R)) with hf`. Establish `hfρ : T.S.u.map f = ρ.map φ` using `rfl`.

Establish `hker : RingHom.ker f = L.im (RingHom.ker j)`. Use extensionality with `a`. Simplify using `only [hf, RingHom.mem_ker, Space.Loc.im, Ideal.mem_comap, RingHom.comp_apply, map_eq_zero_iff _ hφi]`. Both sides reduce to the same expression. Establish `hTE : T.S.u.TE (RingHom.ker f)`.

Rewrite using `[hker]`. Take `⟨a, b, c⟩` from `hid (RingHom.ker j)`. Conclude with `⟨⟨fun h => hE.1.1 (a.2 h), fun h => hE.1.2 (b.2 h)⟩, rfl, c.1 hE.2.2⟩`. Establish `hirr` using `typeE T.ok T.S y.Fb f hTE`. Establish `hodd : ∀ g a b, Odd (w 3 a - w 3 b) → ρ.r g a b = 0` using `fun g a b h => hE.2.2 (Ideal.subset_span ⟨g, a, b, h, rfl⟩)`.

Establish `hV : Nonempty T.G.Vl`. Rewrite using `[T.K.e.nonempty_congr]`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_nonempty_iff]`. Use `T.big.1` as an intermediate fact.

Simplify using `[Frame.d] at this`. Take `⟨v⟩` from `hV`. Establish `hfi : U.FiniteIndex` using `by haveI : CompactSpace T.G.G₀ := isCompact_iff_compactSpace.1 (T.G.η.ker.isClosed_of_isOpen T.G.η_open).isCompact haveI := U.quotient_finite_of_isOpen hU`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`. Establish `hU' : IsOpen (U.normalCore : Set T.G.G₀)` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (U.isClosed_of_isOpen hU))`.

Take `⟨g₁, hg₁, hfree⟩` from `niceSep l O F 3 T x L y j hj hN hρ hψ _ hU' v`. Use `haveI : T.G.G'.Normal := MonoidHom.normal_ker _`. Set `lam : T.G.Gv v →* F.Gv (T.K.e v)` to `(T.K.lam v).toMulEquiv.toMonoidHom`. Establish `hlam : ∀ s, T.K.π (T.G.φ v s) = F.loc0 _ (lam s)` using `fun s => (T.K.lam_loc v s).symm`. Set `k' : ResidueField O →+* ResidueField y.A` to `(ResidueField.map (j : L.R →+* y.A)).comp (ResidueField.map (algebraMap O L.R))`.

Establish `hres : ∀ z : L.R, residue y.A (j z) = ResidueField.map (j : L.R →+* y.A) (residue L.R z)` using `fun z => (ResidueField.map_residue (j : L.R →+* y.A) z).symm`. Establish `key` using `core (ρ.r.comp T.K.π) (fun g => ⟨hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide)⟩) φ hφi (fun W hW => hirr W fun g _ u hu => by`. Take `⟨g', rfl⟩` from `T.K.π_surj g`. Conclude with `hW g' trivial u hu)`. Use the proof step `(residue y.A) (fun a => W.pushCh k' (((F.Ψ.comp F.del.ker.subtype).comp T.K.π) ^ w 3 (![0, 2] a)))`.

Use the proof step `(fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 0))) (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 2)))`. Use the proof step `(fun g => by`. Distinguish the cases in `hx : T.S.u.triP ≤ x`. Establish `h1 : L.ρ.r (T.K.π g) 2 0 ∈ maximalIdeal L.R`. Use `hx (Ideal.subset_span ⟨T.K.π g, 2, 0, by decide, rfl⟩)` as an intermediate fact.

Rewrite `this` using `[← L.lies]`. Conclude with `this`. Use `mul_eq_zero_of_right _ ((hres _).trans ?_)` and prove the remaining obligations. Rewrite using `[(residue_eq_zero_iff _).2 h1, map_zero]`. Establish `h1 : L.ρ.r (T.K.π g) 0 2 ∈ maximalIdeal L.R` using `(htri hx).2 (Ideal.subset_span ⟨T.K.π g, 0, 2, by decide, rfl⟩)`.

Use `mul_eq_zero_of_left ((hres _).trans ?_) _` and prove the remaining obligations. Rewrite using `[(residue_eq_zero_iff _).2 h1, map_zero])`. Use the proof step `(T.G.φ v) (fun i => ((ρ.map φ).ψ (T.K.e v) i).comp lam)`. Use the proof step `(fun g => by`. Establish `h` using `congrArg (Polynomial.map f) (o1 T.ok T.n23 T.S (T.K.e v) (lam g))`.

Rewrite `h` using `[← Matrix.charpoly_map, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h`. Rewrite using `[MonoidHom.comp_apply, hlam]`. Conclude with `h)`. Use the proof step `(fun g => by`.

Establish `h` using `(ρ.map φ).ord (T.K.e v) fun i => lam (g i)`. Simplify using `only [MonoidHom.comp_apply, hlam]`. Conclude with `h)`. Use the proof step `(U.normalCore ⊓ T.G.G') ⟨g₁, hg₁, fun a b hab e => hfree a b hab 1 one_pos (by`. Establish `e1 : φ (ρ.ψ (T.K.e v) a (lam g₁)) = φ (ρ.ψ (T.K.e v) b (lam g₁))` using `congrArg Units.val e`.

Establish `e2 : ρ.ψ (T.K.e v) a (lam g₁) = ρ.ψ (T.K.e v) b (lam g₁)` using `Units.ext (hφi e1)`. Establish `e3 : y.ψ v a g₁ = y.ψ v b g₁`. Rewrite using `[hψ]`. Conclude with `congrArg (· * _) e2`. Simplify using `only [e3])⟩`.

Use the proof step `(by`. Take `⟨g, hg⟩` from `T.ok.f3 (T.K.e v)`. Take `⟨s, rfl⟩` from `(T.K.lam v).surjective g`. Use `⟨s, fun e => hg ?_⟩` and prove the remaining obligations. Establish `e1 : k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 0 : (ResidueField O)ˣ) : ResidueField O) = k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 2 : (ResidueField O)ˣ) : ResidueField O)` using `congrArg Units.val e`.

Establish `e2` using `Units.ext (k'.injective e1)`. Rewrite `e2` using `[hlam, show w 3 0 = 1 by decide, show w 3 2 = -1 by decide, zpow_one, _root_.zpow_neg_one]`. Rewrite using `[sq]`. Conclude with `mul_eq_one_iff_eq_inv.2 e2)`. Introduce `Y hW`.

Use `key Y fun g hg u hu => ?_` and prove the remaining obligations. Establish `h1` using `hW g ⟨U.normalCore_le hg.1, hg.2⟩ u hu`. Establish `h2 : (W.mat (W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] = φ (T.K.κA y.A g) • (((ρ.r.comp T.K.π) g).map φ).submatrix ![0, 2] ![0, 2]`. Use extensionality with `a b`. Use `show φ (UpperTheory.V.W.mat y.ρ g _ _) = _`.

Rewrite using `[hρ]`. Conclude with `map_mul φ _ _`. Simplify using `only [h2, smul_mulVec] at h1`. Conclude with `(Y.smul_mem_iff (((T.K.κA y.A g).isUnit.map φ).ne_zero)).1 h1`.
-/
theorem UpperTheory.V.Pr.niceIrrE :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TE (RingHom.ker j) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → UpperTheory.V.U3.MatIrr (U ⊓ T.G.G') fun g => (UpperTheory.V.W.mat (UpperTheory.V.W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] := by
  intro l _ O _ _ _ _ _ F T x L y j hj hN hρ hψ hE U hU
  have hj' : IsLocalHom (j : L.R →+* y.A) := ⟨hj.map_nonunit⟩
  obtain ⟨-, hbar, hid, htri⟩ := loc_rho T.ok T.n23 T.S x L
  have hO : IsLocalHom (algebraMap O L.R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 := ha.map j
    rw [AlgHom.commutes, PowerSeries.isUnit_iff_constantCoeff] at h1
    have h2 : residue O a = 0 := (residue_eq_zero_iff a).2 hna
    have h3 : PowerSeries.constantCoeff (algebraMap O y.A a) = algebraMap (ResidueField O) y.K (residue O a) := by
      rw [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, IsScalarTower.algebraMap_apply O (ResidueField O) y.K]
      rfl
    rw [h3, h2, map_zero] at h1
    exact not_isUnit_zero h1
  have hb := (hbar (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _).1
  set φ : y.A →+* y.Fb := (algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr) with hφ
  have hφi : Function.Injective φ := (algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)
  set ρ := L.ρ.map (j : L.R →+* y.A) with hρd
  set f : T.S.A →+* y.Fb := φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R)) with hf
  have hfρ : T.S.u.map f = ρ.map φ := rfl
  have hker : RingHom.ker f = L.im (RingHom.ker j) := by
    ext a
    simp only [hf, RingHom.mem_ker, Space.Loc.im, Ideal.mem_comap, RingHom.comp_apply, map_eq_zero_iff _ hφi]
    rfl
  have hTE : T.S.u.TE (RingHom.ker f) := by
    rw [hker]
    obtain ⟨a, b, c⟩ := hid (RingHom.ker j)
    exact ⟨⟨fun h => hE.1.1 (a.2 h), fun h => hE.1.2 (b.2 h)⟩, rfl, c.1 hE.2.2⟩
  have hirr := typeE T.ok T.S y.Fb f hTE
  have hodd : ∀ g a b, Odd (w 3 a - w 3 b) → ρ.r g a b = 0 := fun g a b h =>
    hE.2.2 (Ideal.subset_span ⟨g, a, b, h, rfl⟩)
  have hV : Nonempty T.G.Vl := by
    rw [T.K.e.nonempty_congr]
    by_contra hc
    rw [not_nonempty_iff] at hc
    have := T.big.1
    simp [Frame.d] at this
  obtain ⟨v⟩ := hV
  have hfi : U.FiniteIndex := by
    haveI : CompactSpace T.G.G₀ :=
      isCompact_iff_compactSpace.1 (T.G.η.ker.isClosed_of_isOpen T.G.η_open).isCompact
    haveI := U.quotient_finite_of_isOpen hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hU' : IsOpen (U.normalCore : Set T.G.G₀) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (U.isClosed_of_isOpen hU))
  obtain ⟨g₁, hg₁, hfree⟩ := niceSep l O F 3 T x L y j hj hN hρ hψ _ hU' v
  haveI : T.G.G'.Normal := MonoidHom.normal_ker _
  let lam : T.G.Gv v →* F.Gv (T.K.e v) := (T.K.lam v).toMulEquiv.toMonoidHom
  have hlam : ∀ s, T.K.π (T.G.φ v s) = F.loc0 _ (lam s) := fun s => (T.K.lam_loc v s).symm
  let k' : ResidueField O →+* ResidueField y.A :=
    (ResidueField.map (j : L.R →+* y.A)).comp (ResidueField.map (algebraMap O L.R))
  have hres : ∀ z : L.R, residue y.A (j z) = ResidueField.map (j : L.R →+* y.A) (residue L.R z) := fun z =>
    (ResidueField.map_residue (j : L.R →+* y.A) z).symm
  have key := core (ρ.r.comp T.K.π)
    (fun g => ⟨hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide)⟩) φ hφi
    (fun W hW => hirr W fun g _ u hu => by
      obtain ⟨g', rfl⟩ := T.K.π_surj g
      exact hW g' trivial u hu)
    (residue y.A) (fun a => W.pushCh k' (((F.Ψ.comp F.del.ker.subtype).comp T.K.π) ^ w 3 (![0, 2] a)))
    (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 0))) (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 2)))
    (fun g => by
      by_cases hx : T.S.u.triP ≤ x
      · have h1 : L.ρ.r (T.K.π g) 2 0 ∈ maximalIdeal L.R := by
          have := hx (Ideal.subset_span ⟨T.K.π g, 2, 0, by decide, rfl⟩)
          rw [← L.lies] at this
          exact this
        refine mul_eq_zero_of_right _ ((hres _).trans ?_)
        rw [(residue_eq_zero_iff _).2 h1, map_zero]
      · have h1 : L.ρ.r (T.K.π g) 0 2 ∈ maximalIdeal L.R :=
          (htri hx).2 (Ideal.subset_span ⟨T.K.π g, 0, 2, by decide, rfl⟩)
        refine mul_eq_zero_of_left ((hres _).trans ?_) _
        rw [(residue_eq_zero_iff _).2 h1, map_zero])
    (T.G.φ v) (fun i => ((ρ.map φ).ψ (T.K.e v) i).comp lam)
    (fun g => by
      have h := congrArg (Polynomial.map f) (o1 T.ok T.n23 T.S (T.K.e v) (lam g))
      rw [← Matrix.charpoly_map, Polynomial.map_prod] at h
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
      rw [MonoidHom.comp_apply, hlam]
      exact h)
    (fun g => by
      have h := (ρ.map φ).ord (T.K.e v) fun i => lam (g i)
      simp only [MonoidHom.comp_apply, hlam]
      exact h)
    (U.normalCore ⊓ T.G.G') ⟨g₁, hg₁, fun a b hab e => hfree a b hab 1 one_pos (by
      have e1 : φ (ρ.ψ (T.K.e v) a (lam g₁)) = φ (ρ.ψ (T.K.e v) b (lam g₁)) := congrArg Units.val e
      have e2 : ρ.ψ (T.K.e v) a (lam g₁) = ρ.ψ (T.K.e v) b (lam g₁) := Units.ext (hφi e1)
      have e3 : y.ψ v a g₁ = y.ψ v b g₁ := by
        rw [hψ]
        exact congrArg (· * _) e2
      simp only [e3])⟩
    (by
      obtain ⟨g, hg⟩ := T.ok.f3 (T.K.e v)
      obtain ⟨s, rfl⟩ := (T.K.lam v).surjective g
      refine ⟨s, fun e => hg ?_⟩
      have e1 : k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 0 : (ResidueField O)ˣ) : ResidueField O) =
          k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 2 : (ResidueField O)ˣ) : ResidueField O) := congrArg Units.val e
      have e2 := Units.ext (k'.injective e1)
      rw [hlam, show w 3 0 = 1 by decide, show w 3 2 = -1 by decide, zpow_one, _root_.zpow_neg_one] at e2
      rw [sq]
      exact mul_eq_one_iff_eq_inv.2 e2)
  intro Y hW
  refine key Y fun g hg u hu => ?_
  have h1 := hW g ⟨U.normalCore_le hg.1, hg.2⟩ u hu
  have h2 : (W.mat (W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] =
      φ (T.K.κA y.A g) • (((ρ.r.comp T.K.π) g).map φ).submatrix ![0, 2] ![0, 2] := by
    ext a b
    show φ (UpperTheory.V.W.mat y.ρ g _ _) = _
    rw [hρ]
    exact map_mul φ _ _
  simp only [h2, smul_mulVec] at h1
  exact (Y.smul_mem_iff (((T.K.κA y.A g).isUnit.map φ).ne_zero)).1 h1
