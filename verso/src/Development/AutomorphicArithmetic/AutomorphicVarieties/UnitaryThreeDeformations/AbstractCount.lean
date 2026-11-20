import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.FiniteResidue
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsCoord
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.NormBoundOfIntegralValues
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Origin
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TangentCoordEqZeroOfNonposWeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.PrecompleteOfPowLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.PtSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsPtHomAct
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UnitEqOneOfPowEqOneOfResidueOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TypeIOfTwoSigned
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.NormTwoEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ContinuousCompOfFilteredContinuity
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsUniqueIsPtHom

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `g`. Simplify using `[conjBy, GG.ofGL]`.
-/
private theorem conjBy_one' {R : Type} [CommRing R] {D : Type} [Group D] (r : D →* GG 3 R) :
    conjBy 1 r = r := by
  apply MonoidHom.ext; intro g; simp [conjBy, GG.ofGL]

/- English proof (translation)
Introduce `hM hM' l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hOk hLV hC hVE hCl hX g₁ hm R _ _ _ u hU hfin φ Good hGood hRig`. Take `⟨W, hAd, hMin⟩` from `exists_adapted F hOk g₁ hm u hU`. Take `⟨h, hpush⟩` from `hasOrigin F hOk g₁ hm u hU W hAd`. Take `⟨f, hf, hker⟩` from `exists_relations F hOk hLV hC g₁ hm u hU W hAd hMin`. Establish `hent : ∀ g x y, W.origin h ((u g).mat x y) = (r0 F.η F.Ψ g).mat x y`.

Introduce `g x y`. Conclude with `congrArg (fun q => (q g).mat x y) hpush`. Establish `hpt : ∀ ξ : Sring O u →ₐ[O] PadicAlgCl l, ∃ r, IsPtHom u ξ r` using `fun ξ => (existsUnique_isPtHom u ξ).exists`. Establish `hval : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r → ∀ g x y, ξ ⟨(u g).mat x y, mem_Sring u (entry_mem u g x y)⟩ = (r g).mat x y`. Introduce `ξ r hr g x y`.

Rewrite using `[(hr g).2]`. Both sides reduce to the same expression. Establish `halg : ∀ c : O, algebraMap O R c ∈ wpart O u 0`. Introduce `c R' _ _ _ f₁ f₂ t _`. Simplify using the standard rewrite rules.

Establish `hdiag : ∀ i : Fin 3, (u φ).mat i i ∈ wpart O u 0`. Introduce `i`. Simplify `entry_mem u φ i i` using `[wt]`. Use `set a : R := (u φ).mat.trace - algebraMap O R ((r0 F.η F.Ψ φ).mat.trace) with ha_def`. Establish `ha0 : a ∈ wpart O u 0` using `Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => hdiag i) (halg _)`.

Establish `hξa : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r → ξ ⟨a, mem_Sring u ha0⟩ = (r φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace`. Introduce `ξ r hr`. Establish `hsplit : (⟨a, mem_Sring u ha0⟩ : Sring O u) = ∑ i, ⟨(u φ).mat i i, mem_Sring u (hdiag i)⟩ - algebraMap O (Sring O u) ((r0 F.η F.Ψ φ).mat.trace)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[a, Matrix.trace]`.

Rewrite using `[hsplit, map_sub, map_sum, AlgHom.commutes]`. Simplify using `only [Matrix.trace, Matrix.diag]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => hval ξ r hr φ i i`. Simplify using `[Frame.rz, map_sum]`.

Establish `hao : W.origin h a = 0`. Simplify using `[a, Matrix.trace, map_sum, hent]`. Establish `hfacts : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r → (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) → (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) → F.IsCharZeroPt g₁ r ∧ TypeI F.η r ∧ Good r`. Introduce `ξ r hr hneg hpos`. Establish `hs` using `isPtHom_sign F hOk g₁ hm u hU ξ r hr`.

Establish `hz` using `isCharZeroPt_of_isPtHom F hOk g₁ hm u hU hfin ξ r hr`. Establish `hT` using `typeI_of_twoSigned F hOk hLV hX g₁ hm r hz (fun h' => hneg (hs.1.1 h')) (fun h' => hpos (hs.2.1 h'))`. Conclude with `⟨hz, hT, hGood ξ r hr hT⟩`. Establish `hwt2 : ∀ x y : Fin 3, -2 ≤ wt x y ∧ wt x y ≤ 2`. Introduce `x y`.

Apply the tactic sequence `fin_cases x <;> fin_cases y <;> simp [wt, wt1]`. Establish `hwt : ∀ s : W.σ, -2 ≤ W.wt s ∧ W.wt s ≤ 2`. Introduce `s`. Take `⟨g, x, y, -, hw, -⟩` from `hAd.var s`. Rewrite using `[hw]`.

Conclude with `hwt2 x y`. Establish `hcard : ∀ j : ℤ, ((Module.finrank (ResidueField O) (F.Ob j) : ℕ) : ℤ) + (if j = -1 then -1 else if j = 1 ∨ j = 2 then 1 else 0) ≤ (Nat.card {i // W.wt i = j} : ℤ)`. Introduce `j`. Take `⟨-, -, hd⟩` from `hC j`. Establish `hle` using `finrank_H1L_le F hOk hLV hC g₁ hm u hU W hAd j`.

Express the relevant statement in the definitionally equal form `_ + Frame.defect j ≤ _`. Rewrite using `[← hd]`. Use linear arithmetic over natural numbers and integers. Establish `horig : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l), (∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) → (∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) → ∀ (j : ℤ) (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = algebraMap O (PadicAlg …`. Introduce `ξ hneg hpos j x hx`.

Take `⟨r, hr⟩` from `hpt ξ`. Establish `hs` using `isPtHom_sign F hOk g₁ hm u hU ξ r hr`. Establish `hz` using `isCharZeroPt_of_isPtHom F hOk g₁ hm u hU hfin ξ r hr`. Establish `hrz` using `eq_rz_of_diag F hOk hCl g₁ hm r hz (hs.1.2 hneg) (hs.2.2 hpos)`. Set `ξ0 : Sring O u →ₐ[O] PadicAlgCl l` to `(Algebra.ofId O (PadicAlgCl l)).comp ((W.origin h).comp (Sring O u).val)`.

Establish `h0 : IsPtHom u ξ0 (F.rz (PadicAlgCl l))`. Introduce `g`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrz]`. Conclude with `(hr g).1`.

Use extensionality with `x y`. Simplify using `[ptMat, ξ0, Frame.rz, hent]`. Establish `hr' : IsPtHom u ξ (conjBy ((tor (PadicAlgCl l)) 1) (F.rz (PadicAlgCl l)))`. Rewrite using `[map_one, conjBy_one', ← hrz]`. Conclude with `hr`.

Use `(isPtHom_act F hOk g₁ hm u hU hfin ξ0 _ h0 ξ 1).1 hr' j x hx` as an intermediate fact. Simplify `this` using `[ξ0]`. Establish `hder : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l), (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) → (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) → ∀ D ∈ PtDer ξ (PadicAlgCl l), ∃ c, ∀ (j : ℤ) (x : R) (hx : x ∈ wpart O u j), D ⟨x, mem_ …`. Introduce `ξ hneg hpos D hD`. Take `⟨r, hr⟩` from `hpt ξ`.

Take `⟨hz, hT, hG⟩` from `hfacts ξ r hr hneg hpos`. Conclude with `tangent_eq_orbit F hOk g₁ hm u hU hfin ξ r hr (hRig r hz hT hG).1 D hD`. Establish `hne : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l), (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) → (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) → ξ ⟨a, mem_Sring u ha0⟩ ≠ 0`. Introduce `ξ hneg hpos`. Take `⟨r, hr⟩` from `hpt ξ`.

Take `⟨hz, hT, hG⟩` from `hfacts ξ r hr hneg hpos`. Rewrite using `[hξa ξ r hr]`. Conclude with `sub_ne_zero.mpr (hRig r hz hT hG).2`. Take `⟨n, ξs, V, hnt, hinj, hlen, hV⟩` from `Abs.coord_count hM hM' O (PadicAlgCl l) (fun x => ((Base.eO l O).toNat : ℝ) * vl1 l x) norm_bound_of_integral_values R W h (wpart O u) hAd.part hwt (fun j => Module.finrank (ResidueField O) (F.Ob j)) f hf hker hcard (tangent_coord_eq_zero_of_nonpos_weight F hOk hVE g₁ hm u hU W h …`. Use `choose rr hrr using hpt`.

Use `⟨n, fun i => rr (ξs i), V, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Conclude with `hfacts (ξs i) _ (hrr _) (hnt i).1 (hnt i).2`. Introduce `i i' hiso`. Take `⟨hz, hT, -⟩` from `hfacts (ξs i) _ (hrr _) (hnt i).1 (hnt i).2`.

Take `⟨hz', -, -⟩` from `hfacts (ξs i') _ (hrr _) (hnt i').1 (hnt i').2`. Take `⟨t, ht⟩` from `conj_of_matIso F hOk g₁ hm _ hz _ hz' hT hiso`. Apply `hinj i i' t` to reduce the goal to its premises. Establish `h2` using `hrr (ξs i')`. Rewrite `h2` using `[ht]`.

Conclude with `(isPtHom_act F hOk g₁ hm u hU hfin (ξs i) _ (hrr _) (ξs i') t).1 h2`. Introduce `c hc`. Take `⟨d, hdi, hd1, hd2⟩` from `mprime_coord F hOk g₁ hm u hU W hAd c hc`. Conclude with `hlen c hc _ d hdi hd1 hd2`. Establish `hsum : ∀ i, ξs i ⟨a, mem_Sring u ha0⟩ = (rr (ξs i) φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace` using `fun i => hξa _ _ (hrr _)`.

Simplify using `only [hsum] at hV`. Rewrite using `[mul_assoc, Finset.mul_sum]`. Conclude with `hV`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.abstract_count :
    LemmaM → LemmaM' → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [FaithfulSMul O (PadicAlgCl l)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → F.Count → F.VanE → F.Cl1 → F.Xpp → ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    Module.Finite O (wpart O u 0) → ∀ (φ : Γ) (Good : (Γ →* GG 3 (PadicAlgCl l)) → Prop),
      (∀ (ξ : Sring O u →ₐ[O] (PadicAlgCl l)) (r : Γ →* GG 3 (PadicAlgCl l)), IsPtHom u ξ r → TypeI F.η r → Good r) →
      (∀ r, F.IsCharZeroPt g₁ r → TypeI F.η r → Good r → F.Rigid r ∧ (r φ).mat.trace ≠ (F.rz (PadicAlgCl l) φ).mat.trace) →
      ∃ (n : ℕ) (r : Fin n → (Γ →* GG 3 (PadicAlgCl l))) (V : ℕ), (∀ i, F.IsCharZeroPt g₁ (r i) ∧ TypeI F.η (r i) ∧ Good (r i)) ∧
        (∀ i i', MatIso F.η.ker (mats (r i)) (mats (r i')) → i = i') ∧ (∀ a : O, a ≠ 0 → F.shaLen a ≤ V) ∧
        (V : ℝ) ≤ 2 * (Base.eO l O).toNat * ∑ i, vl1 l ((r i φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace) := by
  intro hM hM' l _ O _ _ _ _ _ _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hOk hLV hC hVE hCl hX g₁ hm R _ _ _ u hU hfin φ Good hGood hRig
  obtain ⟨W, hAd, hMin⟩ := exists_adapted F hOk g₁ hm u hU
  obtain ⟨h, hpush⟩ := hasOrigin F hOk g₁ hm u hU W hAd
  obtain ⟨f, hf, hker⟩ := exists_relations F hOk hLV hC g₁ hm u hU W hAd hMin
  have hent : ∀ g x y, W.origin h ((u g).mat x y) = (r0 F.η F.Ψ g).mat x y := by
    intro g x y
    exact congrArg (fun q => (q g).mat x y) hpush
  have hpt : ∀ ξ : Sring O u →ₐ[O] PadicAlgCl l, ∃ r, IsPtHom u ξ r :=
    fun ξ => (existsUnique_isPtHom u ξ).exists
  have hval : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r → ∀ g x y,
      ξ ⟨(u g).mat x y, mem_Sring u (entry_mem u g x y)⟩ = (r g).mat x y := by
    intro ξ r hr g x y
    rw [(hr g).2]
    rfl
  have halg : ∀ c : O, algebraMap O R c ∈ wpart O u 0 := by
    intro c R' _ _ _ f₁ f₂ t _
    simp
  have hdiag : ∀ i : Fin 3, (u φ).mat i i ∈ wpart O u 0 := by
    intro i
    simpa [wt] using entry_mem u φ i i
  set a : R := (u φ).mat.trace - algebraMap O R ((r0 F.η F.Ψ φ).mat.trace) with ha_def
  have ha0 : a ∈ wpart O u 0 :=
    Submodule.sub_mem _ (Submodule.sum_mem _ fun i _ => hdiag i) (halg _)
  have hξa : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r →
      ξ ⟨a, mem_Sring u ha0⟩ = (r φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace := by
    intro ξ r hr
    have hsplit : (⟨a, mem_Sring u ha0⟩ : Sring O u) =
        ∑ i, ⟨(u φ).mat i i, mem_Sring u (hdiag i)⟩ - algebraMap O (Sring O u) ((r0 F.η F.Ψ φ).mat.trace) := by
      apply Subtype.ext
      simp [a, Matrix.trace]
    rw [hsplit, map_sub, map_sum, AlgHom.commutes]
    simp only [Matrix.trace, Matrix.diag]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => hval ξ r hr φ i i
    · simp [Frame.rz, map_sum]
  have hao : W.origin h a = 0 := by
    simp [a, Matrix.trace, map_sum, hent]
  have hfacts : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l) r, IsPtHom u ξ r →
      (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      F.IsCharZeroPt g₁ r ∧ TypeI F.η r ∧ Good r := by
    intro ξ r hr hneg hpos
    have hs := isPtHom_sign F hOk g₁ hm u hU ξ r hr
    have hz := isCharZeroPt_of_isPtHom F hOk g₁ hm u hU hfin ξ r hr
    have hT := typeI_of_twoSigned F hOk hLV hX g₁ hm r hz (fun h' => hneg (hs.1.1 h')) (fun h' => hpos (hs.2.1 h'))
    exact ⟨hz, hT, hGood ξ r hr hT⟩
  have hwt2 : ∀ x y : Fin 3, -2 ≤ wt x y ∧ wt x y ≤ 2 := by
    intro x y
    fin_cases x <;> fin_cases y <;> simp [wt, wt1]
  have hwt : ∀ s : W.σ, -2 ≤ W.wt s ∧ W.wt s ≤ 2 := by
    intro s
    obtain ⟨g, x, y, -, hw, -⟩ := hAd.var s
    rw [hw]
    exact hwt2 x y
  have hcard : ∀ j : ℤ, ((Module.finrank (ResidueField O) (F.Ob j) : ℕ) : ℤ) +
      (if j = -1 then -1 else if j = 1 ∨ j = 2 then 1 else 0) ≤ (Nat.card {i // W.wt i = j} : ℤ) := by
    intro j
    obtain ⟨-, -, hd⟩ := hC j
    have hle := finrank_H1L_le F hOk hLV hC g₁ hm u hU W hAd j
    change _ + Frame.defect j ≤ _
    rw [← hd]
    omega
  have horig : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l),
      (∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      (∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      ∀ (j : ℤ) (x : R) (hx : x ∈ wpart O u j),
        ξ ⟨x, mem_Sring u hx⟩ = algebraMap O (PadicAlgCl l) (W.origin h x) := by
    intro ξ hneg hpos j x hx
    obtain ⟨r, hr⟩ := hpt ξ
    have hs := isPtHom_sign F hOk g₁ hm u hU ξ r hr
    have hz := isCharZeroPt_of_isPtHom F hOk g₁ hm u hU hfin ξ r hr
    have hrz := eq_rz_of_diag F hOk hCl g₁ hm r hz (hs.1.2 hneg) (hs.2.2 hpos)
    let ξ0 : Sring O u →ₐ[O] PadicAlgCl l :=
      (Algebra.ofId O (PadicAlgCl l)).comp ((W.origin h).comp (Sring O u).val)
    have h0 : IsPtHom u ξ0 (F.rz (PadicAlgCl l)) := by
      intro g
      refine ⟨?_, ?_⟩
      · rw [← hrz]
        exact (hr g).1
      · ext x y
        simp [ptMat, ξ0, Frame.rz, hent]
    have hr' : IsPtHom u ξ (conjBy ((tor (PadicAlgCl l)) 1) (F.rz (PadicAlgCl l))) := by
      rw [map_one, conjBy_one', ← hrz]
      exact hr
    have := (isPtHom_act F hOk g₁ hm u hU hfin ξ0 _ h0 ξ 1).1 hr' j x hx
    simpa [ξ0] using this
  have hder : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l),
      (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      ∀ D ∈ PtDer ξ (PadicAlgCl l), ∃ c, ∀ (j : ℤ) (x : R) (hx : x ∈ wpart O u j),
        D ⟨x, mem_Sring u hx⟩ = c * j * ξ ⟨x, mem_Sring u hx⟩ := by
    intro ξ hneg hpos D hD
    obtain ⟨r, hr⟩ := hpt ξ
    obtain ⟨hz, hT, hG⟩ := hfacts ξ r hr hneg hpos
    exact tangent_eq_orbit F hOk g₁ hm u hU hfin ξ r hr (hRig r hz hT hG).1 D hD
  have hne : ∀ (ξ : Sring O u →ₐ[O] PadicAlgCl l),
      (¬∀ j < 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      (¬∀ j > 0, ∀ (x : R) (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) →
      ξ ⟨a, mem_Sring u ha0⟩ ≠ 0 := by
    intro ξ hneg hpos
    obtain ⟨r, hr⟩ := hpt ξ
    obtain ⟨hz, hT, hG⟩ := hfacts ξ r hr hneg hpos
    rw [hξa ξ r hr]
    exact sub_ne_zero.mpr (hRig r hz hT hG).2
  obtain ⟨n, ξs, V, hnt, hinj, hlen, hV⟩ :=
    Abs.coord_count hM hM' O (PadicAlgCl l) (fun x => ((Base.eO l O).toNat : ℝ) * vl1 l x) norm_bound_of_integral_values
      R W h (wpart O u) hAd.part hwt (fun j => Module.finrank (ResidueField O) (F.Ob j)) f hf hker
      hcard (tangent_coord_eq_zero_of_nonpos_weight F hOk hVE g₁ hm u hU W hAd) hfin horig hder a ha0 hao hne
  choose rr hrr using hpt
  refine ⟨n, fun i => rr (ξs i), V, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hfacts (ξs i) _ (hrr _) (hnt i).1 (hnt i).2
  · intro i i' hiso
    obtain ⟨hz, hT, -⟩ := hfacts (ξs i) _ (hrr _) (hnt i).1 (hnt i).2
    obtain ⟨hz', -, -⟩ := hfacts (ξs i') _ (hrr _) (hnt i').1 (hnt i').2
    obtain ⟨t, ht⟩ := conj_of_matIso F hOk g₁ hm _ hz _ hz' hT hiso
    apply hinj i i' t
    have h2 := hrr (ξs i')
    rw [ht] at h2
    exact (isPtHom_act F hOk g₁ hm u hU hfin (ξs i) _ (hrr _) (ξs i') t).1 h2
  · intro c hc
    obtain ⟨d, hdi, hd1, hd2⟩ := mprime_coord F hOk g₁ hm u hU W hAd c hc
    exact hlen c hc _ d hdi hd1 hd2
  · have hsum : ∀ i, ξs i ⟨a, mem_Sring u ha0⟩ =
        (rr (ξs i) φ).mat.trace - (F.rz (PadicAlgCl l) φ).mat.trace := fun i => hξa _ _ (hrr _)
    simp only [hsum] at hV
    rw [mul_assoc, Finset.mul_sum]
    exact hV
