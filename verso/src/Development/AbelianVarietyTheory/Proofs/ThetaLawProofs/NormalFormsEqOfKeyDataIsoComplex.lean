import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyPBId
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyIsoNormal

abbrev pt : Sp ℂ := (default : PrimeSpectrum ℂ)

def toStalk : ℂ →+* (Sp ℂ).presheaf.stalk pt :=
  ((Sp ℂ).presheaf.germ ⊤ pt trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

/- English proof (translation)
Establish `h'` using `(top_le_preimage_iff_mem x U).2 h`. Rewrite using `[gs_eq x pt U h, valAt', dif_pos h', valAt, toStalk, RingHom.comp_apply]`. Use `erw [(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply]`. Conclude with `(TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') pt trivial _).symm`.
-/
theorem gs_eq_toStalk {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : x pt ∈ U) (f : Γ(X, U)) :
    gs x pt U f = toStalk (valAt' x U f) := by
  have h' := (top_le_preimage_iff_mem x U).2 h
  rw [gs_eq x pt U h, valAt', dif_pos h', valAt, toStalk, RingHom.comp_apply]
  erw [(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE h') pt trivial _).symm

/- English proof (translation)
The claim follows from `(gs_unit x pt U h f).symm.trans (gs_eq_toStalk x U h _)`.
-/
theorem gm_eq_toStalk {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : x pt ∈ U) (f : Γ(X, U)ˣ) :
    (gm x pt U f).val = toStalk (valAt' x U f.val) :=
  (gs_unit x pt U h f).symm.trans (gs_eq_toStalk x U h _)

section Unit

variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

def wv (w : LB.Iso L' (L.pull F)) (y : Sp ℂ ⟶ X') (j : L.ι) (k : L'.ι) : ℂ :=
  valAt' y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w.s (fun _ => j, k)).val

/- English proof (translation)
The claim follows from `gm_eq_toStalk y ((L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _`.
-/
theorem gw_eq_toStalk (w : LB.Iso L' (L.pull F)) (y : Sp ℂ ⟶ X') {j : L.ι} {k : L'.ι} (hj : F (y pt) ∈ L.U j)
    (hk : y pt ∈ L'.U k) : (gw w y pt j k).val = toStalk (wv w y j k) :=
  gm_eq_toStalk y ((L.pull F).U (fun _ => j) ⊓ L'.U k) ⟨mem_pull.2 hj, hk⟩ _

/- English proof (translation)
Introduce `h` and use `(gw w y pt j k).ne_zero (by rw [gw_eq_toStalk w y hj hk, h, map_zero])`.
-/
theorem wv_ne_zero (w : LB.Iso L' (L.pull F)) (y : Sp ℂ ⟶ X') {j : L.ι} {k : L'.ι} (hj : F (y pt) ∈ L.U j)
    (hk : y pt ∈ L'.U k) : wv w y j k ≠ 0 := fun h =>
  (gw w y pt j k).ne_zero (by rw [gw_eq_toStalk w y hj hk, h, map_zero])

/- English proof (translation)
Apply `toStalk.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← gw_eq_toStalk w y hj hk, ← gw_eq_toStalk w y hj' hk', ← gm_eq_toStalk y (L'.U k ⊓ L'.U k') ⟨hk, hk'⟩, ← gm_eq_toStalk (y ≫ F) (L.U j ⊓ L.U j') ⟨hj, hj'⟩, hw _ y pt j j' k k' hj hj' hk hk', ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right …`.
-/
theorem wv_compat {w : LB.Iso L' (L.pull F)} (hw : PGen w) (y : Sp ℂ ⟶ X') {j j' : L.ι} {k k' : L'.ι}
    (hj : F (y pt) ∈ L.U j) (hj' : F (y pt) ∈ L.U j') (hk : y pt ∈ L'.U k) (hk' : y pt ∈ L'.U k') :
    wv w y j k * valAt' y (L'.U k ⊓ L'.U k') (L'.g k k').val =
      valAt' (y ≫ F) (L.U j ⊓ L.U j') (L.g j j').val * wv w y j' k' := by
  apply toStalk.injective
  rw [map_mul, map_mul, ← gw_eq_toStalk w y hj hk, ← gw_eq_toStalk w y hj' hk',
    ← gm_eq_toStalk y (L'.U k ⊓ L'.U k') ⟨hk, hk'⟩, ← gm_eq_toStalk (y ≫ F) (L.U j ⊓ L.U j') ⟨hj, hj'⟩,
    hw _ y pt j j' k k' hj hj' hk hk', ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right]

end Unit

/- English proof (translation)
Set `e : T ⟶ Over.mk (T.hom ≫ 𝟙 S)` to `Over.homMk (𝟙 T.left) (by simp)`. Set `l : (T ⟶ A') → (Over.mk (T.hom ≫ 𝟙 S) ⟶ A)` to `fun x => Over.homMk (x ≫ ψ).left (by simp)`. Establish `hl : ∀ x, e ≫ l x = x ≫ ψ` using `fun x => by ext; simp [e, l]`. Use `h.2 T x y (l x) (l y) rfl rfl` as an intermediate fact. Rewrite using `[← hl x, ← hl y, ← MonObj.comp_mul]`.

Use `ext`. Rewrite using `[Over.comp_left, Over.comp_left, this]`. Simplify using `[e]`.
-/
theorem comp_mul_of_isGrpPullback {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (ψ : A' ⟶ A)
    (h : IsGrpPullback A' A (𝟙 S) ψ.left) {T : Over S} (x y : T ⟶ A') : (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ) := by
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 S) := Over.homMk (𝟙 T.left) (by simp)
  let l : (T ⟶ A') → (Over.mk (T.hom ≫ 𝟙 S) ⟶ A) := fun x => Over.homMk (x ≫ ψ).left (by simp)
  have hl : ∀ x, e ≫ l x = x ≫ ψ := fun x => by ext; simp [e, l]
  have := h.2 T x y (l x) (l y) rfl rfl
  rw [← hl x, ← hl y, ← MonObj.comp_mul]
  ext
  rw [Over.comp_left, Over.comp_left, this]
  simp [e]

/- English proof (translation)
Establish `: IsIso ψ.left` using `h.1.isIso_fst_of_isIso`. Establish `: IsIso ((Over.forget _).map ψ)` using `this`. Establish `: IsIso ψ` using `isIso_of_reflects_iso ψ (Over.forget _)`. Establish `hm` using `fun x y : 𝟙_ (Over (Sp ℂ)) ⟶ A' => comp_mul_of_isGrpPullback ψ h x y`. Establish `h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A') ≫ ψ = 1`.

Use `hm 1 1` as an intermediate fact. Rewrite `this` using `[_root_.mul_one]`. Conclude with `mul_eq_left.1 this.symm`. Use `choose K hK using fun z => exists_chart hL' ((u'.ex z).left pt)`. Establish `key : ∀ j k z, ψ.left ((u'.ex z).left pt) ∈ L.U j → (u'.ex z).left pt ∈ L'.U k → wv w (u'.ex z).left j (K z) * u'.fr (K z) z = wv w (u'.ex z).left j k * u'.fr k z` using `fun j k z hj hk => by`.

Establish `e` using `wv_compat hw (u'.ex z).left hj hj (hK z) hk`. Establish `e' : valAt' ((u'.ex z).left ≫ ψ.left) (L.U j ⊓ L.U j) (L.g j j).val = 1`. Apply `toStalk.injective` to reduce the goal to its premises. Rewrite using `[← gm_eq_toStalk _ (L.U j ⊓ L.U j) ⟨hj, hj⟩, gm_self hL ((u'.ex z).left ≫ ψ.left) pt hj, map_one, Units.val_one]`. Rewrite `e` using `[e', _root_.one_mul]`.

Rewrite using `[u'.fr_compat (K z) k z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hk⟩), ← _root_.mul_assoc, e]`. Establish `mem : ∀ (U : A.left.Opens) z, ⊤ ≤ (u'.ex z ≫ ψ).left ⁻¹ᵁ U → ψ.left ((u'.ex z).left pt) ∈ U` using `fun U z hz => (top_le_preimage_iff_mem _ _).1 hz`. Use `⟨ { ex := fun z => u'.ex z ≫ ψ ex_add := fun z z' => by rw [u'.ex_add, hm] ex_onto := fun p => (u'.ex_onto (p ≫ inv ψ)).imp fun z hz => by simp [hz] Λ := u'.Λ ker := fun z => by rw [← u'.ker, ← h1, cancel_mono] discrete := u'.discrete full := u'.full hol := fun U f => by` and prove the remaining obligations. Use `u'.hol (ψ.left ⁻¹ᵁ U) ((ψ.left.app U).hom f)` as an intermediate fact. Simplify using `only [valAt'_comp] at this`.

Conclude with `this`. Use `fr := fun j z => wv w (u'.ex z).left j (K z) * u'.fr (K z) z`. Use `fr_hol := fun j z hz => ?_`. Use `fr_ne := fun j z hz => mul_ne_zero (wv_ne_zero w _ (mem _ _ hz) (hK z)) (u'.fr_ne _ _ ((top_le_preimage_iff_mem _ _).2 (hK z)))`. Use `fr_compat := fun j j' z hz => ?_ }, fun _ => rfl, rfl, key⟩`.

Take `⟨ho, hd⟩` from `u'.hol ((L.pull ψ.left).U (fun _ => j) ⊓ L'.U (K z)) (w.s (fun _ => j, K z)).val`. Establish `hn` using `ho.mem_nhds ((top_le_preimage_iff_mem _ _).2 ⟨mem_pull.2 (mem _ _ hz), hK z⟩)`. Establish `hn'` using `(u'.hol (L'.U (K z)) 0).1.mem_nhds ((top_le_preimage_iff_mem _ _).2 (hK z))`. Use `(((hd.differentiableAt hn).mul ((u'.fr_hol (K z)).differentiableAt hn')).congr_of_eventuallyEq ?_).differentiableWithinAt` and prove the remaining obligations. Use `filter_upwards [hn] with y hy`.

Establish `hy'` using `(top_le_preimage_iff_mem _ _).1 hy`. Conclude with `key j (K z) y (mem_pull.1 hy'.1) hy'.2`. Establish `hz'` using `mem _ _ hz`. Establish `e` using `wv_compat hw (u'.ex z).left hz'.1 hz'.2 (hK z) (hK z)`. Rewrite using `[u'.fr_compat (K z) (K z) z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hK z⟩), ← _root_.mul_assoc, e, _root_.mul_assoc, ← u'.fr_compat (K z) (K z) z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hK z⟩)]`.

Both sides reduce to the same expression.
-/
theorem exists_push {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (ψ : A' ⟶ A) (h : IsGrpPullback A' A (𝟙 _) ψ.left) (w : LB.Iso L' (L.pull ψ.left)) (hw : PGen w)
    {g : ℕ} (u' : HolUnif A' L' g) :
    ∃ u : HolUnif A L g, (∀ z, (u.ex z).left = (u'.ex z).left ≫ ψ.left) ∧ u.Λ = u'.Λ ∧
      ∀ j k z, ψ.left ((u'.ex z).left pt) ∈ L.U j → (u'.ex z).left pt ∈ L'.U k →
        u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := by
  have : IsIso ψ.left := h.1.isIso_fst_of_isIso
  have : IsIso ((Over.forget _).map ψ) := this
  have : IsIso ψ := isIso_of_reflects_iso ψ (Over.forget _)
  have hm := fun x y : 𝟙_ (Over (Sp ℂ)) ⟶ A' => comp_mul_of_isGrpPullback ψ h x y
  have h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A') ≫ ψ = 1 := by
    have := hm 1 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  choose K hK using fun z => exists_chart hL' ((u'.ex z).left pt)
  have key : ∀ j k z, ψ.left ((u'.ex z).left pt) ∈ L.U j → (u'.ex z).left pt ∈ L'.U k →
      wv w (u'.ex z).left j (K z) * u'.fr (K z) z = wv w (u'.ex z).left j k * u'.fr k z := fun j k z hj hk => by
    have e := wv_compat hw (u'.ex z).left hj hj (hK z) hk
    have e' : valAt' ((u'.ex z).left ≫ ψ.left) (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
      apply toStalk.injective
      rw [← gm_eq_toStalk _ (L.U j ⊓ L.U j) ⟨hj, hj⟩, gm_self hL ((u'.ex z).left ≫ ψ.left) pt hj, map_one, Units.val_one]
    rw [e', _root_.one_mul] at e
    rw [u'.fr_compat (K z) k z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hk⟩), ← _root_.mul_assoc, e]
  have mem : ∀ (U : A.left.Opens) z, ⊤ ≤ (u'.ex z ≫ ψ).left ⁻¹ᵁ U → ψ.left ((u'.ex z).left pt) ∈ U :=
    fun U z hz => (top_le_preimage_iff_mem _ _).1 hz
  refine ⟨
    { ex := fun z => u'.ex z ≫ ψ
      ex_add := fun z z' => by rw [u'.ex_add, hm]
      ex_onto := fun p => (u'.ex_onto (p ≫ inv ψ)).imp fun z hz => by simp [hz]
      Λ := u'.Λ
      ker := fun z => by rw [← u'.ker, ← h1, cancel_mono]
      discrete := u'.discrete
      full := u'.full
      hol := fun U f => by
        have := u'.hol (ψ.left ⁻¹ᵁ U) ((ψ.left.app U).hom f)
        simp only [valAt'_comp] at this
        exact this
      fr := fun j z => wv w (u'.ex z).left j (K z) * u'.fr (K z) z
      fr_hol := fun j z hz => ?_
      fr_ne := fun j z hz => mul_ne_zero (wv_ne_zero w _ (mem _ _ hz) (hK z))
        (u'.fr_ne _ _ ((top_le_preimage_iff_mem _ _).2 (hK z)))
      fr_compat := fun j j' z hz => ?_ }, fun _ => rfl, rfl, key⟩
  · obtain ⟨ho, hd⟩ := u'.hol ((L.pull ψ.left).U (fun _ => j) ⊓ L'.U (K z)) (w.s (fun _ => j, K z)).val
    have hn := ho.mem_nhds ((top_le_preimage_iff_mem _ _).2 ⟨mem_pull.2 (mem _ _ hz), hK z⟩)
    have hn' := (u'.hol (L'.U (K z)) 0).1.mem_nhds ((top_le_preimage_iff_mem _ _).2 (hK z))
    refine (((hd.differentiableAt hn).mul ((u'.fr_hol (K z)).differentiableAt hn')).congr_of_eventuallyEq
      ?_).differentiableWithinAt
    filter_upwards [hn] with y hy
    have hy' := (top_le_preimage_iff_mem _ _).1 hy
    exact key j (K z) y (mem_pull.1 hy'.1) hy'.2
  · have hz' := mem _ _ hz
    have e := wv_compat hw (u'.ex z).left hz'.1 hz'.2 (hK z) (hK z)
    rw [u'.fr_compat (K z) (K z) z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hK z⟩), ← _root_.mul_assoc, e,
      _root_.mul_assoc, ← u'.fr_compat (K z) (K z) z ((top_le_preimage_iff_mem _ _).2 ⟨hK z, hK z⟩)]
    rfl

def NormalIn (x : KeyIn ℂ) {g : ℕ} (h : x.P.g = g) (τ M : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) : Prop :=
  ∃ u : HolUnif x.P.A x.P.L g,
    τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧
    (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
    u.IsRig x.rig ∧ u.IsFn x.th (fun z => c * thetaChar τ a b z) ∧
    ∀ i, u.IsDiff ((2 * Real.pi * Complex.I)⁻¹ • M i) (x.v (i.cast h.symm))

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem val_iff (x : KeyIn ℂ) {g : ℕ} (h : x.P.g = g) (t : ℂ) :
    Val x t ↔ ∃ (τ M : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ),
      charHalf _ a b ∧ c ≠ 0 ∧ NormalIn x h τ M a b c ∧ t = M.det ^ 4 / c ^ 8 := by
  subst h
  rfl

/- English proof (translation)
Use `exists_congr fun h => ?_` and prove the remaining obligations. Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem nrm_iff (x : KeyIn ℂ) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) :
    Nrm x τ a b ↔ ∃ (h : x.P.g = g) (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ), c ≠ 0 ∧ NormalIn x h τ M a b c := by
  refine exists_congr fun h => ?_
  subst h
  rfl

/- English proof (translation)
Take `⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩` from `H`. Take `⟨u', h₁, h₂, h₃, h₄, h₅, h₆⟩` from `hN`. Establish `hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ)` using `Spec.map_id _`. Establish `hFid : spMap F = 𝟙 _`. Rewrite using `[KeyCancel.dualNumber_ringHom_ext (F := F) (G := RingHom.id _) hF hFe]`.

Conclude with `Spec.map_id _`. Establish `r` using `(maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap (RingHom.id ℂ)) _ (rigPull_le φ (spMap (RingHom.id ℂ)) he x.P.L) (fun _ => rfl)).1 hr`. Rewrite `r`, `he` using `[hid]`. Rewrite `he` using `[Category.id_comp]`. Establish `hc'` using `hc.congr hid rfl`.

Take `⟨u, hex, hΛ, hfr⟩` from `exists_push x.P.isLB x'.P.isLB (Over.homMk φ (hc'.1.w.trans (Category.comp_id _))) hc' w ((isGen_iff w).1 hw) u'`. Use `replace hex : ∀ z, (u.ex z).left = (u'.ex z).left ≫ φ := hex`. Use `replace hfr : ∀ j k z, φ ((u'.ex z).left pt) ∈ x.P.L.U j → (u'.ex z).left pt ∈ x'.P.L.U k → u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := hfr`. Use `⟨u, h₁, h₂, hΛ ▸ h₃, fun j hj => ?_, fun j z hz => ?_, fun i U hU f => ?_⟩` and prove the remaining obligations. Establish `h0 : (u'.ex 0).left = eSec x'.P.A`.

Rewrite using `[(u'.ker 0).2 u'.Λ.zero_mem]`. Express the relevant statement in the definitionally equal form `(toUnit _ ≫ η[x'.P.A]).left = η[x'.P.A].left`. Rewrite using `[toUnit_unit, Category.id_comp]`. Take `⟨k, hk⟩` from `exists_chart x'.P.isLB (eSec x'.P.A pt)`. Establish `hj' : φ (eSec x'.P.A pt) ∈ x.P.L.U (j PUnit.unit)`.

Use `mem_pull.1 (hj (Set.mem_univ pt))` as an intermediate fact. Rewrite `this` using `[← he]`. Conclude with `this`. Establish `hk' : (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) pt ∈ (x'.P.L.pull (eSec x'.P.A)).U (fun _ => k)` using `mem_pull.2 hk`. Establish `e` using `congrArg Units.val (r _ (𝟙 (Sp ℂ)) pt j (fun _ => k) (fun _ => hj') (fun _ => hk))`.

Rewrite `e` using `[Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, Units.val_mul]`. Rewrite using `[hfr _ k 0 (h0 ▸ hj') (h0 ▸ hk), h0, h₄ (fun _ => k) ((top_le_preimage_iff_mem (𝟙 _) _).2 hk')]`. Apply `toStalk.injective` to reduce the goal to its premises. Rewrite using `[map_mul]`. Conclude with `(congrArg₂ (· * ·) (gw_eq_toStalk w _ hj' hk).symm (gm_eq_toStalk _ _ hk' _).symm).trans (e.symm.trans (gm_eq_toStalk _ _ (hj (Set.mem_univ pt)) _))`.

Rewrite `hz`, the goal using `[hex]`. Establish `hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j` using `(top_le_preimage_iff_mem _ _).1 hz`. Take `⟨k, hk⟩` from `exists_chart x'.P.isLB ((u'.ex z).left pt)`. Establish `e` using `(KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs _ (u'.ex z).left pt j k hj hk`. Rewrite `e` using `[gs_eq_toStalk _ _ hj, gs_eq_toStalk _ _ hk, gw_eq_toStalk w _ hj hk, ← map_mul]`.

Rewrite using `[toStalk.injective e, hfr j k z hj hk, h₅ k z ((top_le_preimage_iff_mem _ _).2 hk)]`. Expand and normalize the polynomial expressions, which then agree. Establish `e : (x.v (i.cast h.symm)).left = (x'.v (i.cast h'.symm)).left ≫ φ`. Rewrite using `[hv, hFid, Category.id_comp]`. Both sides reduce to the same expression.

Use `h₆ i (φ ⁻¹ᵁ U) (by rw [e] at hU; exact hU) ((φ.app U).hom f)` as an intermediate fact. Simplify using `only [valAt'_comp, ← hex] at this`. Rewrite using `[← this]`. Use `congr 2`. Generalize the expression as in `(x.v (i.cast h.symm)).left = q at e hU`.

Substitute `e` using the available equality. Rewrite using `[Scheme.Hom.comp_appLE]`. Both sides reduce to the same expression.
-/
theorem NormalIn.push {x x' : KeyIn ℂ} (H : KeyPB x' x (RingHom.id ℂ)) {g : ℕ} (h : x.P.g = g) (h' : x'.P.g = g)
    {τ M : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {c : ℂ} (hN : NormalIn x' h' τ M a b c) :
    NormalIn x h τ M a b c := by
  obtain ⟨φ, he, w, hg, F, hc, hw, hr, hs, hF, hFe, hv⟩ := H
  obtain ⟨u', h₁, h₂, h₃, h₄, h₅, h₆⟩ := hN
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hFid : spMap F = 𝟙 _ := by
    rw [KeyCancel.dualNumber_ringHom_ext (F := F) (G := RingHom.id _) hF hFe]
    exact Spec.map_id _
  have r := (maps_iff w _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap (RingHom.id ℂ)) _
    (rigPull_le φ (spMap (RingHom.id ℂ)) he x.P.L) (fun _ => rfl)).1 hr
  rw [hid] at r he
  rw [Category.id_comp] at he
  have hc' := hc.congr hid rfl
  obtain ⟨u, hex, hΛ, hfr⟩ := exists_push x.P.isLB x'.P.isLB (Over.homMk φ (hc'.1.w.trans (Category.comp_id _))) hc' w
    ((isGen_iff w).1 hw) u'
  replace hex : ∀ z, (u.ex z).left = (u'.ex z).left ≫ φ := hex
  replace hfr : ∀ j k z, φ ((u'.ex z).left pt) ∈ x.P.L.U j → (u'.ex z).left pt ∈ x'.P.L.U k →
    u.fr j z = wv w (u'.ex z).left j k * u'.fr k z := hfr
  refine ⟨u, h₁, h₂, hΛ ▸ h₃, fun j hj => ?_, fun j z hz => ?_, fun i U hU f => ?_⟩
  · have h0 : (u'.ex 0).left = eSec x'.P.A := by
      rw [(u'.ker 0).2 u'.Λ.zero_mem]
      change (toUnit _ ≫ η[x'.P.A]).left = η[x'.P.A].left
      rw [toUnit_unit, Category.id_comp]
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB (eSec x'.P.A pt)
    have hj' : φ (eSec x'.P.A pt) ∈ x.P.L.U (j PUnit.unit) := by
      have := mem_pull.1 (hj (Set.mem_univ pt))
      rw [← he] at this
      exact this
    have hk' : (𝟙 (Sp ℂ) : Sp ℂ ⟶ Sp ℂ) pt ∈ (x'.P.L.pull (eSec x'.P.A)).U (fun _ => k) := mem_pull.2 hk
    have e := congrArg Units.val (r _ (𝟙 (Sp ℂ)) pt j (fun _ => k) (fun _ => hj') (fun _ => hk))
    rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp, Units.val_mul] at e
    rw [hfr _ k 0 (h0 ▸ hj') (h0 ▸ hk), h0, h₄ (fun _ => k) ((top_le_preimage_iff_mem (𝟙 _) _).2 hk')]
    apply toStalk.injective
    rw [map_mul]
    exact (congrArg₂ (· * ·) (gw_eq_toStalk w _ hj' hk).symm (gm_eq_toStalk _ _ hk' _).symm).trans
      (e.symm.trans (gm_eq_toStalk _ _ (hj (Set.mem_univ pt)) _))
  · rw [hex] at hz ⊢
    have hj : φ ((u'.ex z).left pt) ∈ x.P.L.U j := (top_le_preimage_iff_mem _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart x'.P.isLB ((u'.ex z).left pt)
    have e := (KeyCancel.appLE_eq_iff_stalk w x.th x'.th).1 hs _ (u'.ex z).left pt j k hj hk
    rw [gs_eq_toStalk _ _ hj, gs_eq_toStalk _ _ hk, gw_eq_toStalk w _ hj hk, ← map_mul] at e
    rw [toStalk.injective e, hfr j k z hj hk, h₅ k z ((top_le_preimage_iff_mem _ _).2 hk)]
    ring
  · have e : (x.v (i.cast h.symm)).left = (x'.v (i.cast h'.symm)).left ≫ φ := by
      rw [hv, hFid, Category.id_comp]
      rfl
    have := h₆ i (φ ⁻¹ᵁ U) (by rw [e] at hU; exact hU) ((φ.app U).hom f)
    simp only [valAt'_comp, ← hex] at this
    rw [← this]
    congr 2
    generalize (x.v (i.cast h.symm)).left = q at e hU
    subst e
    rw [Scheme.Hom.comp_appLE]
    rfl

/- English proof (translation)
Introduce `x x' H`. Establish `H' : KeyPB x x' (RingHom.id ℂ)` using `KeyCancel.keyPB_cancel ℂ ℂ ℂ x x' x (RingHom.id ℂ) (RingHom.id ℂ) H (keyPB_id ℂ x)`. Establish `hg : x'.P.g = x.P.g`. Take `⟨-, -, -, hg, -⟩` from `H`. Conclude with `hg`.

Use `⟨fun t => ?_, fun g τ a b => ?_⟩` and prove the remaining obligations. Rewrite using `[val_iff x rfl, val_iff x' hg]`. Conclude with `⟨fun ⟨τ, M, a, b, c, h₁, h₂, h₃, h₄⟩ => ⟨τ, M, a, b, c, h₁, h₂, h₃.push H' hg rfl, h₄⟩, fun ⟨τ, M, a, b, c, h₁, h₂, h₃, h₄⟩ => ⟨τ, M, a, b, c, h₁, h₂, h₃.push H rfl hg, h₄⟩⟩`. Rewrite using `[nrm_iff, nrm_iff]`. Conclude with `⟨fun ⟨h, M, c, h₁, h₂⟩ => ⟨hg.trans h, M, c, h₁, h₂.push H' _ h⟩, fun ⟨h, M, c, h₁, h₂⟩ => ⟨hg.symm.trans h, M, c, h₁, h₂.push H _ h⟩⟩`.
-/
theorem val_iff_and_nrm_iff : ∀ x x' : KeyIn ℂ, KeyPB x' x (RingHom.id ℂ) → (∀ t, Val x t ↔ Val x' t) ∧ ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), Nrm x τ a b ↔ Nrm x' τ a b := by
  intro x x' H
  have H' : KeyPB x x' (RingHom.id ℂ) :=
    KeyCancel.keyPB_cancel ℂ ℂ ℂ x x' x (RingHom.id ℂ) (RingHom.id ℂ) H (keyPB_id ℂ x)
  have hg : x'.P.g = x.P.g := by
    obtain ⟨-, -, -, hg, -⟩ := H
    exact hg
  refine ⟨fun t => ?_, fun g τ a b => ?_⟩
  · rw [val_iff x rfl, val_iff x' hg]
    exact ⟨fun ⟨τ, M, a, b, c, h₁, h₂, h₃, h₄⟩ => ⟨τ, M, a, b, c, h₁, h₂, h₃.push H' hg rfl, h₄⟩,
      fun ⟨τ, M, a, b, c, h₁, h₂, h₃, h₄⟩ => ⟨τ, M, a, b, c, h₁, h₂, h₃.push H rfl hg, h₄⟩⟩
  · rw [nrm_iff, nrm_iff]
    exact ⟨fun ⟨h, M, c, h₁, h₂⟩ => ⟨hg.trans h, M, c, h₁, h₂.push H' _ h⟩,
      fun ⟨h, M, c, h₁, h₂⟩ => ⟨hg.symm.trans h, M, c, h₁, h₂.push H _ h⟩⟩

end GlobalTheory.KeyIsoNormal
end
