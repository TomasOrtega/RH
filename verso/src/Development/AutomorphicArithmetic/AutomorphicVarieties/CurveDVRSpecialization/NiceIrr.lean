import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IrrNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IrrOfConn
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

open IsLocalRing Matrix Polynomial UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.W UpperTheory.V.Pr

/- English proof (translation)
Use `letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra`. Rewrite using `[← Matrix.charpoly_map]`. Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det`. Use `congr 1`. Use extensionality with `i j : 1`.

Establish `h : ∀ a, algebraMap A K[X] a = C (f a)` using `fun _ => rfl`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[GDet.repAlg, h]`. Simplify using `[GDet.repAlg, h, hij]`.
-/
private theorem chi_map_ofRep {n : ℕ} {A K G : Type} [CommRing A] [CommRing K] [Group G] (f : A →+* K)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    ((GDet.ofRep ρ).map f).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly.map f := by
  letI : Algebra A K[X] := ((algebraMap K K[X]).comp f).toAlgebra
  rw [← Matrix.charpoly_map]
  change (GDet.repAlg ρ K[X] _).det = (Matrix.charmatrix _).det
  congr 1
  ext i j : 1
  have h : ∀ a, algebraMap A K[X] a = C (f a) := fun _ => rfl
  by_cases hij : i = j
  · subst hij
    simp [GDet.repAlg, h]
  · simp [GDet.repAlg, h, hij]

/- English proof (translation)
Take `⟨g, hg⟩` from `h`. Establish `h1` using `Matrix.charpoly_units_conj g (gm r s)`. Establish `h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id` using `fun i j hij => (hg s).1 i j hij`. Establish `h3` using `Matrix.charpoly_of_upperTriangular _ h2`. Rewrite using `[← h1]`.

Simplify using `only [Units.val_mul, Matrix.coe_units_inv] at h3`. Rewrite using `[h3]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h4` using `(hg s).2 i`. Simplify using `only [Units.val_mul, Matrix.coe_units_inv] at h4`.

Rewrite using `[h4]`.
-/
private theorem charpoly_flag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k)
    (κ : Fin n → H →* kˣ) (h : HasFlag r κ) (s : H) : (gm r s).charpoly = chPoly κ s := by
  obtain ⟨g, hg⟩ := h
  have h1 := Matrix.charpoly_units_conj g (gm r s)
  have h2 : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).BlockTriangular id :=
    fun i j hij => (hg s).1 i j hij
  have h3 := Matrix.charpoly_of_upperTriangular _ h2
  rw [← h1]
  simp only [Units.val_mul, Matrix.coe_units_inv] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h4 := (hg s).2 i
  simp only [Units.val_mul, Matrix.coe_units_inv] at h4
  rw [h4]

/- English proof (translation)
Introduce `W hW`. Use `hb W fun s _ v hv => ?_` and prove the remaining obligations. Take `⟨g, rfl⟩` from `hπ s`. Establish `h1` using `W.smul_mem ((c g)⁻¹ : kˣ) (hW g trivial v hv)`. Rewrite `h1` using `[h, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul]`. Then use the resulting hypothesis.
-/
private theorem irr_twist {G H k : Type} [Group G] [Group H] [Field k] {n : ℕ} (a : G → Matrix (Fin n) (Fin n) k)
    (b : H → Matrix (Fin n) (Fin n) k) (π : G → H) (hπ : Function.Surjective π) (c : G → kˣ)
    (h : ∀ g, a g = (c g : k) • b (π g)) (hb : MatIrr ⊤ b) : MatIrr ⊤ a := by
  intro W hW
  refine hb W fun s _ v hv => ?_
  obtain ⟨g, rfl⟩ := hπ s
  have h1 := W.smul_mem ((c g)⁻¹ : kˣ) (hW g trivial v hv)
  rwa [h, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at h1

/- English proof (translation)
Break down `hn with rfl | rfl` into its components or cases. Use `⟨0, 1, fun h => ha ?_⟩` and prove the remaining obligations. Establish `h1 : a ^ (1 : ℤ) = a ^ (-1 : ℤ)` using `h`. Rewrite `h1` using `[zpow_one, _root_.zpow_neg_one]`. Rewrite using `[sq]`.

Conclude with `mul_eq_one_iff_eq_inv.2 h1`. Use `⟨0, 2, fun h => ha ?_⟩` and prove the remaining obligations. Establish `h1 : a ^ (1 : ℤ) = a ^ (-1 : ℤ)` using `h`. Rewrite `h1` using `[zpow_one, _root_.zpow_neg_one]`. Rewrite using `[sq]`.

Conclude with `mul_eq_one_iff_eq_inv.2 h1`.
-/
private theorem w_ne {k : Type} [Field k] {n : ℕ} (hn : n = 2 ∨ n = 3) (a : kˣ) (ha : a ^ 2 ≠ 1) :
    ∃ i j : Fin n, a ^ w n i ≠ a ^ w n j := by
  rcases hn with rfl | rfl
  · refine ⟨0, 1, fun h => ha ?_⟩
    have h1 : a ^ (1 : ℤ) = a ^ (-1 : ℤ) := h
    rw [zpow_one, _root_.zpow_neg_one] at h1
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 h1
  · refine ⟨0, 2, fun h => ha ?_⟩
    have h1 : a ^ (1 : ℤ) = a ^ (-1 : ℤ) := h
    rw [zpow_one, _root_.zpow_neg_one] at h1
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 h1

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ F n T x L y j hj hp h1 h2 hI U hU`. Set `φ : y.A →+* y.Fb` to `(algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr)`. Establish `hφ : Function.Injective φ` using `(algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)`. Establish `hm : ∀ g, gm (pushRep (algebraMap y.Fr y.Fb) y.ρF) g = (mat y.ρ g).map φ` using `fun g => rfl`. Establish `hn : n.Prime`.

Break down `T.n23 with rfl | rfl` into its components or cases. Conclude with `Nat.prime_two`. Conclude with `Nat.prime_three`. Establish `hirr : MatIrr ⊤ (gm (pushRep (algebraMap y.Fr y.Fb) y.ρF))`. Set `f : T.S.A →+* y.Fb` to `φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R))`.

Establish `hker : RingHom.ker f = L.im (RingHom.ker j)`. Use extensionality with `a`. Conclude with `(map_eq_zero_iff φ hφ).trans Iff.rfl`. Take `⟨k1, k2, k3⟩` from `(loc_rho T.ok T.n23 T.S x L).2.2.1 (RingHom.ker j)`. Establish `hTI : T.S.u.TI (RingHom.ker f)`.

Rewrite using `[hker]`. Conclude with `⟨⟨fun h => hI.1.1 (k1.2 h), fun h => hI.1.2 (k2.2 h)⟩, fun h3 h => hI.2 h3 (k3.2 h)⟩`. Use `irr_twist _ _ T.K.π T.K.π_surj (fun g => Units.map φ.toMonoidHom (T.K.κA y.A g)) (fun g => ?_) ((types T.ok T.n23 T.S y.Fb f).1.2 hTI)` and prove the remaining obligations. Rewrite using `[hm, h1]`. Use extensionality with `a b`.

Conclude with `map_mul φ _ _`. Establish `hred : RedTo (pushRep (algebraMap y.Fr y.Fb) y.ρF) φ (PowerSeries.constantCoeff : y.A →+* y.K) fun i => pushCh (algebraMap (ResidueField O) y.K) (T.r.chib i)`. Introduce `g`. Use `⟨(mat y.ρ g).charpoly, by rw [hm, Matrix.charpoly_map], ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) y.red`.

Simplify using `only [Resid.Dbar, chi_map_ofRep] at h`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `(Matrix.diagonal _).charpoly.map _ = _`. Rewrite using `[Matrix.charpoly_diagonal, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`.

Both sides reduce to the same expression. Establish `hV : Nonempty F.V`. Assume the negation of the conclusion as `hV`. Rewrite `hV` using `[not_nonempty_iff]`. Establish `h` using `T.big.1`.

Simplify using `[Frame.d] at h`. Take `⟨v'⟩` from `hV`. Take `⟨v, rfl⟩` from `T.K.e.surjective v'`. Establish `hfi : U.FiniteIndex` using `by haveI : CompactSpace T.G.G₀ := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ T.G.η_open).isCompact haveI := Subgroup.quotient_finite_of_isOpen U hU`. Conclude with `Subgroup.finiteIndex_of_finite_quotient`.

Establish `hUo : IsOpen (U.normalCore : Set T.G.G₀)` using `Subgroup.isOpen_of_isClosed_of_finiteIndex _ (Subgroup.normalCore_isClosed U (Subgroup.isClosed_of_isOpen U hU))`. Use `haveI : T.G.G'.Normal := MonoidHom.normal_ker _`. Establish `key` using `irrNormal T.G.G₀ y.Fb y.K y.A n hn (pushRep (algebraMap y.Fr y.Fb) y.ρF) hirr φ _ _ hφ hred (T.G.Gv v) (T.G.φ v) (fun i => pushCh φ (y.ψ v i)) (fun g => ?_) (U.normalCore ⊓ T.G.G') (fun a b hab => ?_) ?_`. Introduce `W hW`. Conclude with `key W fun g hg => hW g ⟨U.normalCore_le hg.1, hg.2⟩`.

Establish `h` using `congrArg (Polynomial.map (algebraMap y.Fr y.Fb)) (charpoly_flag _ _ (y.flag v) g)`. Rewrite `h` using `[← Matrix.charpoly_map, chPoly, Polynomial.map_prod]`. Simplify using `only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h`. Conclude with `h`. Take `⟨g, hg, hfr⟩` from `niceSep l O F n T x L y j hj hp h1 h2 U.normalCore hUo v`.

Use `⟨g, hg, fun h => hfr a b hab 1 one_pos ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, pow_one]`. Conclude with `Units.ext ((algebraMap y.Fr y.Fb).injective (congrArg Units.val h))`. Take `⟨s, hs⟩` from `T.ok.f3 (T.K.e v)`. Take `⟨g, rfl⟩` from `(T.K.lam v).surjective s`.

Take `⟨a, b, hab⟩` from `w_ne T.n23 _ hs`. Use `⟨a, b, g, fun h => hab ?_⟩` and prove the remaining obligations. Establish `h3 : T.r.chib a (T.G.φ v g) = T.r.chib b (T.G.φ v g)` using `Units.ext ((algebraMap (ResidueField O) y.K).injective (congrArg Units.val h))`. Rewrite `h3` using `[T.K.chib, T.K.chib, ← T.K.lam_loc]`. Conclude with `mul_right_cancel h3`.
-/
theorem UpperTheory.V.Pr.niceIrr :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (n : ℕ) (T : UpperTheory.V.Pr.Setup F n) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TI (RingHom.ker j) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → UpperTheory.V.U3.MatIrr (U ⊓ T.G.G') (UpperTheory.V.W.mat (UpperTheory.V.W.pushRep (algebraMap y.Fr y.Fb) y.ρF)) := by
  intro l _ O _ _ _ _ _ F n T x L y j hj hp h1 h2 hI U hU
  classical
  let φ : y.A →+* y.Fb := (algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr)
  have hφ : Function.Injective φ := (algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)
  have hm : ∀ g, gm (pushRep (algebraMap y.Fr y.Fb) y.ρF) g = (mat y.ρ g).map φ := fun g => rfl
  have hn : n.Prime := by
    rcases T.n23 with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three

  have hirr : MatIrr ⊤ (gm (pushRep (algebraMap y.Fr y.Fb) y.ρF)) := by
    let f : T.S.A →+* y.Fb := φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R))
    have hker : RingHom.ker f = L.im (RingHom.ker j) := by
      ext a
      exact (map_eq_zero_iff φ hφ).trans Iff.rfl
    obtain ⟨k1, k2, k3⟩ := (loc_rho T.ok T.n23 T.S x L).2.2.1 (RingHom.ker j)
    have hTI : T.S.u.TI (RingHom.ker f) := by
      rw [hker]
      exact ⟨⟨fun h => hI.1.1 (k1.2 h), fun h => hI.1.2 (k2.2 h)⟩, fun h3 h => hI.2 h3 (k3.2 h)⟩
    refine irr_twist _ _ T.K.π T.K.π_surj (fun g => Units.map φ.toMonoidHom (T.K.κA y.A g)) (fun g => ?_)
      ((types T.ok T.n23 T.S y.Fb f).1.2 hTI)
    rw [hm, h1]
    ext a b
    exact map_mul φ _ _

  have hred : RedTo (pushRep (algebraMap y.Fr y.Fb) y.ρF) φ (PowerSeries.constantCoeff : y.A →+* y.K)
      fun i => pushCh (algebraMap (ResidueField O) y.K) (T.r.chib i) := by
    intro g
    refine ⟨(mat y.ρ g).charpoly, by rw [hm, Matrix.charpoly_map], ?_⟩
    have h := congrArg (fun D => GDet.chi D (MonoidAlgebra.single g 1)) y.red
    simp only [Resid.Dbar, chi_map_ofRep] at h
    rw [h]
    change (Matrix.diagonal _).charpoly.map _ = _
    rw [Matrix.charpoly_diagonal, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl

  have hV : Nonempty F.V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    have h := T.big.1
    simp [Frame.d] at h
  obtain ⟨v'⟩ := hV
  obtain ⟨v, rfl⟩ := T.K.e.surjective v'

  have hfi : U.FiniteIndex := by
    haveI : CompactSpace T.G.G₀ :=
      isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ T.G.η_open).isCompact
    haveI := Subgroup.quotient_finite_of_isOpen U hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hUo : IsOpen (U.normalCore : Set T.G.G₀) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (Subgroup.normalCore_isClosed U (Subgroup.isClosed_of_isOpen U hU))
  haveI : T.G.G'.Normal := MonoidHom.normal_ker _
  have key := irrNormal T.G.G₀ y.Fb y.K y.A n hn (pushRep (algebraMap y.Fr y.Fb) y.ρF) hirr φ _ _ hφ hred
    (T.G.Gv v) (T.G.φ v) (fun i => pushCh φ (y.ψ v i)) (fun g => ?_) (U.normalCore ⊓ T.G.G') (fun a b hab => ?_) ?_
  · intro W hW
    exact key W fun g hg => hW g ⟨U.normalCore_le hg.1, hg.2⟩
  · have h := congrArg (Polynomial.map (algebraMap y.Fr y.Fb)) (charpoly_flag _ _ (y.flag v) g)
    rw [← Matrix.charpoly_map, chPoly, Polynomial.map_prod] at h
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
    exact h
  · obtain ⟨g, hg, hfr⟩ := niceSep l O F n T x L y j hj hp h1 h2 U.normalCore hUo v
    refine ⟨g, hg, fun h => hfr a b hab 1 one_pos ?_⟩
    rw [pow_one, pow_one]
    exact Units.ext ((algebraMap y.Fr y.Fb).injective (congrArg Units.val h))
  · obtain ⟨s, hs⟩ := T.ok.f3 (T.K.e v)
    obtain ⟨g, rfl⟩ := (T.K.lam v).surjective s
    obtain ⟨a, b, hab⟩ := w_ne T.n23 _ hs
    refine ⟨a, b, g, fun h => hab ?_⟩
    have h3 : T.r.chib a (T.G.φ v g) = T.r.chib b (T.G.φ v g) :=
      Units.ext ((algebraMap (ResidueField O) y.K).injective (congrArg Units.val h))
    rw [T.K.chib, T.K.chib, ← T.K.lam_loc] at h3
    exact mul_right_cancel h3
