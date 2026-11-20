import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.TorsFrame
open GlobalTheory.Points

section Val
variable {K : Type} [Field K] {X Y : Scheme.{0}}

/- English proof (translation)
The claim follows from `valR_res x e h u.val`.
-/
theorem valF_res (x : Sp K ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (u : Γ(X, U)ˣ) :
    valF x V (res e u).val = valF x U u.val := valR_res x e h u.val

/- English proof (translation)
The claim follows from `(valR_comp x g U u.val).symm`.
-/
theorem valF_pullU (x : Sp K ⟶ X) (g : X ⟶ Y) (U : Y.Opens) (u : Γ(Y, U)ˣ) :
    valF x (g ⁻¹ᵁ U) (pullU g U u).val = valF (x ≫ g) U u.val := (valR_comp x g U u.val).symm

/- English proof (translation)
The claim follows from `valR_mul x U h u.val v.val`.
-/
theorem valF_mul (x : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u v : Γ(X, U)ˣ) :
    valF x U (u * v).val = valF x U u.val * valF x U v.val := valR_mul x U h u.val v.val

/- English proof (translation)
Rewrite using `[← Nat.cast_pow, zpow_natCast, Units.val_pow_eq_pow_val]`. Conclude with `valR_pow x U h u.val _`.
-/
theorem valF_zpow_sq (x : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℕ) :
    valF x U (u ^ ((n : ℤ) ^ 2)).val = valF x U u.val ^ (n ^ 2) := by
  rw [← Nat.cast_pow, zpow_natCast, Units.val_pow_eq_pow_val]
  exact valR_pow x U h u.val _

/- English proof (translation)
Rewrite using `[← valF_mul x h, mul_inv_cancel]`. Conclude with `valR_one x U h`.
-/
theorem valF_mul_inv (x : Sp K ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valF x U u.val * valF x U (u⁻¹).val = 1 := by
  rw [← valF_mul x h, mul_inv_cancel]
  exact valR_one x U h

/- English proof (translation)
Introduce `_ hp` and use `⟨h hp, h' hp⟩`.
-/
theorem le_preimage_inf (x : Sp K ⟶ X) {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := fun _ hp => ⟨h hp, h' hp⟩

end Val

section Grp
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

/- English proof (translation)
Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id]`.
-/
theorem comp_mulA {T : Over S} (x : T ⟶ G) (n : ℕ) : x.left ≫ (mulA G n).left = (x ^ n).left := by
  rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]

/- English proof (translation)
Use `show (toUnit _ ≫ η[G]).left = _`. Simplify using `[eSec]`.
-/
theorem one_left (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

/- English proof (translation)
Establish `e` using `congrArg (fun z => z.left) (map_pow (pushHom h G') (𝟙 G') n)`. Use `e.trans ((comp_mulA _ n).symm.trans ?_)` and prove the remaining obligations. Conclude with `congrArg (· ≫ (mulA G n).left) (Category.id_comp φ)`.
-/
theorem mulA_comm (h : IsGrpPullback G' G f φ) (n : ℕ) : (mulA G' n).left ≫ φ = φ ≫ (mulA G n).left := by
  have e := congrArg (fun z => z.left) (map_pow (pushHom h G') (𝟙 G') n)
  refine e.trans ((comp_mulA _ n).symm.trans ?_)
  exact congrArg (· ≫ (mulA G n).left) (Category.id_comp φ)

/- English proof (translation)
Establish `e` using `congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))`. Establish `e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G']` using `by rw [Hom.one_def]; simp`. Rewrite `e` using `[e₁]`. Use `e.trans ((one_left _).trans ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem eSec_comm (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ((one_left _).trans ?_)
  simp

end Grp

section Model
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

/- English proof (translation)
Establish `hle : h ⁻¹ᵁ U ≤ W.ι ⁻¹ᵁ W.ι ''ᵁ (h ⁻¹ᵁ U)` using `(W.ι.preimage_image_eq _).ge`. Establish `hm : W.ι w ∈ W.ι ''ᵁ (h ⁻¹ᵁ U)` using `hle hw`. Establish `hy : ⊤ ≤ x ⁻¹ᵁ (h ⁻¹ᵁ U)`. Use `M.top_le_preimage_pt ⟨_, hm⟩` as an intermediate fact. Rewrite `this` using `[← hx]`.

Conclude with `le_preimage_mono x (W.ι.preimage_image_eq _).le this`. Use `⟨hy, fun f => ⟨_, (W.ι.appIso _).inv.hom ((h.app U).hom f), hm, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hx, valF_eq_valR, valF_eq_valR, valR_comp x h, ← valR_appLE x W.ι hle hy, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]`. Conclude with `valR_res x le_rfl hy _`.
-/
theorem valF_comp_mem {W : M.Z.Opens} {X : Scheme.{0}} (h : W.toScheme ⟶ X) (x : Sp Ω ⟶ W.toScheme)
    (hx : x ≫ W.ι = M.pt) (w : W.toScheme) {U : X.Opens} (hw : h w ∈ U) :
    ⊤ ≤ (x ≫ h) ⁻¹ᵁ U ∧ ∀ f : Γ(X, U), valF (x ≫ h) U f ∈ M.O (W.ι w) := by
  have hle : h ⁻¹ᵁ U ≤ W.ι ⁻¹ᵁ W.ι ''ᵁ (h ⁻¹ᵁ U) := (W.ι.preimage_image_eq _).ge
  have hm : W.ι w ∈ W.ι ''ᵁ (h ⁻¹ᵁ U) := hle hw
  have hy : ⊤ ≤ x ⁻¹ᵁ (h ⁻¹ᵁ U) := by
    have := M.top_le_preimage_pt ⟨_, hm⟩
    rw [← hx] at this
    exact le_preimage_mono x (W.ι.preimage_image_eq _).le this
  refine ⟨hy, fun f => ⟨_, (W.ι.appIso _).inv.hom ((h.app U).hom f), hm, ?_⟩⟩
  rw [← hx, valF_eq_valR, valF_eq_valR, valR_comp x h, ← valR_appLE x W.ι hle hy, ← CommRingCat.comp_apply,
    Scheme.Hom.appIso_inv_appLE]
  exact valR_res x le_rfl hy _

/- English proof (translation)
Use `RatModel.isIntegrallyClosed_O hn z` as an intermediate fact. Establish `h1 : IsIntegral (M.O z) (e ^ m)` using `isIntegral_algebraMap (R := M.O z) (x := ⟨_, h⟩)`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow hm h1)`. Conclude with `hy ▸ y.2`.
-/
theorem mem_O_of_pow (hn : IsNormalScheme M.Z) {z : M.Z} {e : Ω} {m : ℕ} (hm : 0 < m) (h : e ^ m ∈ M.O z) :
    e ∈ M.O z := by
  have := RatModel.isIntegrallyClosed_O hn z
  have h1 : IsIntegral (M.O z) (e ^ m) := isIntegral_algebraMap (R := M.O z) (x := ⟨_, h⟩)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.of_pow hm h1)
  exact hy ▸ y.2

end Model

/- English proof (translation)
Establish `he : x.left ≫ (mulA P.A n).left = eSec P.A`. Rewrite using `[comp_mulA, hx, one_left]`. Conclude with `Category.id_comp _`. Choose the witnesses or unpack the hypotheses as in `⟨jP', h1, h2⟩ : ∃ jP', Set.range (y ≫ eSec P.A) ⊆ P.L.U jP' ∧ (x.left = eSec P.A → jP = jP') := by`. Distinguish the cases in `hxe : x.left = eSec P.A`.

Conclude with `⟨jP, hxe ▸ hj, fun _ => rfl⟩`. Take `⟨i, hi⟩` from `exists_le_preimage_of_iSup_eq_top (y ≫ eSec P.A) P.isLB.cover`. Conclude with `⟨i, (top_le_preimage_iff _ _).1 hi, fun h => (hxe h).elim⟩`. Use `⟨jP', h1, ?_⟩` and prove the remaining obligations. Establish `c0 : x.left ≫ 𝟙 P.A.left = x.left` using `Category.comp_id _`.

Establish `c1 : (baseOver B).hom ≫ eSec P.A = eSec P.A` using `Category.id_comp _`. Establish `H` using `hc (fun _ => jP) (Sum.elim ![jP, jP'] fun _ => jP') (fun _ _ _ => rfl) (by`. Introduce and unpack `(a | a) (b | b) hab`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Both sides reduce to the same expression.

Conclude with `h2 (c0.symm.trans (hab.trans he))`. Conclude with `(h2 (c0.symm.trans (hab.symm.trans he))).symm`. Both sides reduce to the same expression. Use `fin_cases a`. Conclude with `h2 (c0.symm.trans (hab.trans c1))`.

Both sides reduce to the same expression. Use `fin_cases b`. Conclude with `(h2 (c0.symm.trans (hab.symm.trans c1))).symm`. Both sides reduce to the same expression. Use the proof step `rfl) (by`.

Introduce and unpack `a (b | b) hab`. Use `fin_cases b`. Both sides reduce to the same expression. Conclude with `h2 (hab.trans he)`. Conclude with `h2 (hab.trans c1))`.

Establish `m0 : ∀ p, x.left (y p) ∈ P.L.U jP` using `fun p => hj ⟨p, rfl⟩`. Establish `m1 : ∀ p, eSec P.A (y p) ∈ P.L.U jP'` using `fun p => h1 ⟨p, rfl⟩`. Establish `m2 : ∀ p, (x.left ≫ (mulA P.A n).left) (y p) ∈ P.L.U jP'` using `fun p => by rw [he]; exact m1 p`. Establish `l0 : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (Y` using `(baseOver B).left) (fun _ : Fin 1 => x.left) (fun _ => jP) := fun p _ => Set.mem_iInter.2 fun _ => m0 p`. Establish `l1 : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (Y` using `(baseOver B).left) (fun k => x.left ≫ ![𝟙 P.A.left, (mulA P.A n).left] k) ![jP, jP'] := fun p _ => Set.mem_iInter.2 fun k => by fin_cases k`.

Conclude with `m0 p`. Conclude with `m2 p`. Establish `l2 : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (Y` using `(baseOver B).left) (fun _ : Fin 1 => (baseOver B).hom ≫ eSec P.A) (fun _ => jP') := fun p _ => Set.mem_iInter.2 fun _ => m1 p`. Establish `l3 : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (Y` using `(baseOver B).left) (Sum.elim (fun k => x.left ≫ ![𝟙 P.A.left, (mulA P.A n).left] k) (fun _ : Fin 1 => (baseOver B).hom ≫ eSec P.A)) (Sum.elim ![jP, jP'] fun _ => jP') := fun p _ => Set.mem_iInter.2 fun k => by`. Break down `k with k | k` into its components or cases.

Conclude with `Set.mem_iInter.1 (l1 (x := p) trivial) k`. Conclude with `m1 p`. Establish `l4` using `le_preimage_inf (X := (baseOver B).left) y l0 l3`. Establish `H'` using `(valF_res (X := (baseOver B).left) y _ l4 _).symm.trans ((congrArg (fun u => valF (X := (baseOver B).left) y _ (Units.val u)) H).trans (valF_res (X := (baseOver B).left) y _ l4 _))`. Use `(valF_zpow_sq (X := (baseOver B).left) y l0 _ n).symm.trans (H'.trans ((valF_mul (X := (baseOver B).left) y l3 _ _).trans (congrArg₂ (· * ·) ?_ ?_)))` and prove the remaining obligations.

Conclude with `(valF_res (X := (baseOver B).left) y _ l3 _).trans ((valF_res (X := (baseOver B).left) y _ l1 _).trans (valF_pullU (X := (baseOver B).left) y _ _ _))`. Use `(valF_res (X := (baseOver B).left) y _ l3 _).trans ?_` and prove the remaining obligations. Use `(congrArg (fun u => valF (X := (baseOver B).left) y _ (Units.val u)) (zpow_one _)).trans ?_` and prove the remaining obligations. Use `(valF_res (X := (baseOver B).left) y _ l2 _).trans ((valF_pullU (X := (baseOver B).left) y _ _ _).trans ?_)` and prove the remaining obligations. Conclude with `congrArg (fun t : Sp K ⟶ B => valF t _ (rig.s fun _ => jP').val) (Category.comp_id y)`.
-/
theorem frame_val {B : Scheme.{0}} (P : PolAV B) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ)
    (x : baseOver B ⟶ P.A) (hx : x ^ n = 1)
    (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver B).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)))
    (α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]))
    (hc : LB.Gen.Corr P.L _ _ _ _ (powFrame P.A P.L x τ ((n : ℤ) ^ 2))
        (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α x.left) (rigT P.A P.L rig (baseOver B) 1)))
    {K : Type} [Field K] (y : Sp K ⟶ B) (jP : P.L.ι) (hj : Set.range (y ≫ x.left) ⊆ P.L.U jP) :
    ∃ jP', Set.range (y ≫ eSec P.A) ⊆ P.L.U jP' ∧
      valF (X := (baseOver B).left) y _ (τ.s fun _ => jP).val ^ (n ^ 2) =
        valF (y ≫ x.left) _ (α.s ![jP, jP']).val * valF y _ (rig.s fun _ => jP').val := by
  have he : x.left ≫ (mulA P.A n).left = eSec P.A := by
    rw [comp_mulA, hx, one_left]; exact Category.id_comp _
  obtain ⟨jP', h1, h2⟩ : ∃ jP', Set.range (y ≫ eSec P.A) ⊆ P.L.U jP' ∧ (x.left = eSec P.A → jP = jP') := by
    by_cases hxe : x.left = eSec P.A
    · exact ⟨jP, hxe ▸ hj, fun _ => rfl⟩
    · obtain ⟨i, hi⟩ := exists_le_preimage_of_iSup_eq_top (y ≫ eSec P.A) P.isLB.cover
      exact ⟨i, (top_le_preimage_iff _ _).1 hi, fun h => (hxe h).elim⟩
  refine ⟨jP', h1, ?_⟩
  have c0 : x.left ≫ 𝟙 P.A.left = x.left := Category.comp_id _
  have c1 : (baseOver B).hom ≫ eSec P.A = eSec P.A := Category.id_comp _
  have H := hc (fun _ => jP) (Sum.elim ![jP, jP'] fun _ => jP') (fun _ _ _ => rfl) (by
    rintro (a | a) (b | b) hab
    · fin_cases a <;> fin_cases b
      · rfl
      · exact h2 (c0.symm.trans (hab.trans he))
      · exact (h2 (c0.symm.trans (hab.symm.trans he))).symm
      · rfl
    · fin_cases a
      · exact h2 (c0.symm.trans (hab.trans c1))
      · rfl
    · fin_cases b
      · exact (h2 (c0.symm.trans (hab.symm.trans c1))).symm
      · rfl
    · rfl) (by
    rintro a (b | b) hab
    · fin_cases b
      · rfl
      · exact h2 (hab.trans he)
    · exact h2 (hab.trans c1))
  have m0 : ∀ p, x.left (y p) ∈ P.L.U jP := fun p => hj ⟨p, rfl⟩
  have m1 : ∀ p, eSec P.A (y p) ∈ P.L.U jP' := fun p => h1 ⟨p, rfl⟩
  have m2 : ∀ p, (x.left ≫ (mulA P.A n).left) (y p) ∈ P.L.U jP' := fun p => by rw [he]; exact m1 p
  have l0 : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (Y := (baseOver B).left) (fun _ : Fin 1 => x.left) (fun _ => jP) :=
    fun p _ => Set.mem_iInter.2 fun _ => m0 p
  have l1 : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (Y := (baseOver B).left)
      (fun k => x.left ≫ ![𝟙 P.A.left, (mulA P.A n).left] k) ![jP, jP'] :=
    fun p _ => Set.mem_iInter.2 fun k => by
      fin_cases k
      · exact m0 p
      · exact m2 p
  have l2 : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (Y := (baseOver B).left)
      (fun _ : Fin 1 => (baseOver B).hom ≫ eSec P.A) (fun _ => jP') :=
    fun p _ => Set.mem_iInter.2 fun _ => m1 p
  have l3 : ⊤ ≤ y ⁻¹ᵁ LB.wchart P.L (Y := (baseOver B).left)
      (Sum.elim (fun k => x.left ≫ ![𝟙 P.A.left, (mulA P.A n).left] k)
        (fun _ : Fin 1 => (baseOver B).hom ≫ eSec P.A)) (Sum.elim ![jP, jP'] fun _ => jP') :=
    fun p _ => Set.mem_iInter.2 fun k => by
      rcases k with k | k
      · exact Set.mem_iInter.1 (l1 (x := p) trivial) k
      · exact m1 p
  have l4 := le_preimage_inf (X := (baseOver B).left) y l0 l3
  have H' := (valF_res (X := (baseOver B).left) y _ l4 _).symm.trans
    ((congrArg (fun u => valF (X := (baseOver B).left) y _ (Units.val u)) H).trans
      (valF_res (X := (baseOver B).left) y _ l4 _))
  refine (valF_zpow_sq (X := (baseOver B).left) y l0 _ n).symm.trans (H'.trans
    ((valF_mul (X := (baseOver B).left) y l3 _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
  · exact (valF_res (X := (baseOver B).left) y _ l3 _).trans ((valF_res (X := (baseOver B).left) y _ l1 _).trans
      (valF_pullU (X := (baseOver B).left) y _ _ _))
  · refine (valF_res (X := (baseOver B).left) y _ l3 _).trans ?_
    refine (congrArg (fun u => valF (X := (baseOver B).left) y _ (Units.val u)) (zpow_one _)).trans ?_
    refine (valF_res (X := (baseOver B).left) y _ l2 _).trans ((valF_pullU (X := (baseOver B).left) y _ _ _).trans ?_)
    exact congrArg (fun t : Sp K ⟶ B => valF t _ (rig.s fun _ => jP').val) (Category.comp_id y)

/- English proof (translation)
Introduce `o Ω _ _ _ _ S ρ M U₀ Q hO hκ a W h w hE jP jL x' e hw hx1 hx2 hjP he`. Take `⟨hpn, -, α, hα, hN, hc⟩` from `ρ.fr_tors a`. Take `⟨κ, -, hR⟩` from `hκ α hα hN`. Establish `npos : 0 < (S.r * S.N) ^ 2` using `pow_pos (Nat.mul_pos S.r_pos (lt_of_lt_of_le two_pos S.N_ge)) 2`. Generalize the expression as in `S.r * S.N = n at hpn α hα hN hc κ hR npos`.

Use `clear hκ`. Use `set y : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom with hy`. Take `⟨jP', hjP', hF⟩` from `frame_val ρ.P ρ.rig n (ρ.pt a) hpn (ρ.fr a) α hc y jP (hx2 ▸ hjP)`. Establish `hWne : (W : Set M.Z).Nonempty` using `⟨w.1, w.2⟩`. Set `x : Sp Ω ⟶ W.toScheme` to `IsOpenImmersion.lift W.ι M.pt (by`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `(top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hWne))`. Establish `hx : x ≫ W.ι = M.pt` using `IsOpenImmersion.lift_fac _ _ _`. Establish `hxh : x ≫ h = x' ≫ Q.φ` using `hE.2 x x' hx hx1 hx2`. Establish `s1 : (x' ≫ pullback.snd _ _) ≫ U₀.ι = M.pt`.

Rewrite using `[← hx1, Q.cart.1.w]`. Conclude with `Category.assoc _ _ _`. Establish `s2 : (x' ≫ pullback.snd _ _) ≫ Q.u₀ = y` using `Q.u₀_gen _ s1`. Establish `hb` using `isGrpPullback_pullback ρ.P.A Q.u₀`. Set `g' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀` to `x' ≫ (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n).left`.

Establish `g1 : g' ≫ pullback.fst _ _ = x' ≫ pullback.fst _ _ ≫ (mulA ρ.P.A n).left` using `(Category.assoc _ _ _).trans (congrArg (x' ≫ ·) (mulA_comm hb n))`. Establish `g2 : g' ≫ pullback.snd _ _ = x' ≫ pullback.snd _ _` using `(Category.assoc _ _ _).trans (congrArg (x' ≫ ·) (Over.w (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n)))`. Establish `g3 : g' ≫ pullback.fst _ _ = y ≫ eSec ρ.P.A`. Rewrite using `[g1, ← Category.assoc, hx2, Category.assoc]`. Use `congrArg (y ≫ ·) ((comp_mulA _ n).trans ?_)` and prove the remaining obligations.

Rewrite using `[hpn, one_left]`. Conclude with `Category.id_comp _`. Establish `g4 : g' = (x' ≫ pullback.snd _ _) ≫ eSec ((Over.pullback Q.u₀).obj ρ.P.A)`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[g3, ← s2]`.

Conclude with `(Category.assoc _ _ _).trans ((congrArg ((x' ≫ pullback.snd _ _) ≫ ·) (eSec_comm hb).symm).trans (Category.assoc _ _ _).symm)`. Rewrite using `[g2]`. Conclude with `(Category.comp_id _).symm.trans ((congrArg ((x' ≫ pullback.snd _ _) ≫ ·) (Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]).symm).trans (Category.assoc _ _ _).symm)`. Establish `g5 : g' ≫ Q.φ = M.pt ≫ eSec Q.G`. Establish `e1` using `eSec_comm Q.cart`.

Rewrite using `[g4, ← s1]`. Conclude with `(Category.assoc _ _ _).trans ((congrArg ((x' ≫ pullback.snd _ _) ≫ ·) e1).trans (Category.assoc _ _ _).symm)`. Establish `g6 : g' ≫ Q.φ = x' ≫ Q.φ ≫ (mulA Q.G n).left` using `(Category.assoc _ _ _).trans (congrArg (x' ≫ ·) (mulA_comm Q.cart n))`. Establish `hdom : IsDominant x`. Establish `: IsDominant (x ≫ W.ι)` using `hx ▸ M.isDominant_pt`.

Conclude with `⟨W.ι.isOpenEmbedding.isInducing.dense_iff.2 fun p => by`. Rewrite using `[← Set.range_comp]`. Conclude with `this.1 _⟩`. Establish `hsep : IsSeparated Q.G.hom` using `Q.semi.separated`. Establish `hmul : h ≫ (mulA Q.G n).left = W.ι ≫ eSec Q.G`.

Use `ext_of_isDominant_of_isSeparated Q.G.hom ?_ x ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Over.w, hE.1, Category.assoc]`. Conclude with `((congrArg (W.ι ≫ ·) (Over.w η[Q.G])).trans (Category.comp_id _)).symm`. Rewrite using `[← Category.assoc, hxh, Category.assoc, ← g6, g5, ← hx, Category.assoc]`. Take `⟨jL', hjL'⟩ : ∃ j, eSec Q.G (W.ι w) ∈ Q.L.L.U j` from `TopologicalSpace.Opens.mem_iSup.1 (Q.L.isLB.cover.ge trivial)`.

Establish `k1 : h w ∈ LB.wchart Q.L.L ![𝟙 Q.G.left, (mulA Q.G n).left] ![jL, jL']` using `Set.mem_iInter.2 fun k => by fin_cases k`. Conclude with `hw`. Use `show (h ≫ (mulA Q.G n).left) w ∈ Q.L.L.U jL'`. Rewrite using `[hmul]`. Conclude with `hjL'`.

Establish `k2 : W.ι w ∈ LB.wchart Q.L.L (fun _ : PUnit => eSec Q.G) (fun _ => jL')` using `Set.mem_iInter.2 fun _ => hjL'`. Take `⟨a1, b1⟩` from `valF_comp_mem h x hx w k1`. Take `⟨a2, b2⟩` from `valF_comp_mem W.ι x hx w k2`. Rewrite `a1`, `b1` using `[hxh]`. Rewrite `a2`, `b2` using `[hx]`.

Establish `r1 : Set.range (x' ≫ Q.φ) ⊆ Q.L.L.U jL`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `Set.mem_iInter.1 (a1 (x := p) trivial) 0`. Establish `r2 : Set.range (g' ≫ Q.φ) ⊆ Q.L.L.U jL'`. Rewrite using `[g5]`.

Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `Set.mem_iInter.1 (a2 (x := p) trivial) PUnit.unit`. Establish `r3 : Set.range (g' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP'` using `g3 ▸ hjP'`. Establish `E1` using `hR Ω x' g' jP jP' jL jL' g1 g2 hjP r1 r3 r2`. Establish `E2` using `Q.w_rig Ω g' M.pt y jP' jL' g5 g3 r3 r2`.

Establish `a3 : ⊤ ≤ x' ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U (fun _ => jP, fun _ => jL)` using `fun p _ => ⟨Set.mem_iInter.2 fun _ => hjP ⟨p, rfl⟩, Set.mem_iInter.2 fun _ => r1 ⟨p, rfl⟩⟩`. Establish `u3` using `left_ne_zero_of_mul_eq_one (valF_mul_inv x' a3 (Q.w.s (fun _ => jP, fun _ => jL)))`. Establish `u1` using `valF_mul_inv _ a1 (κ.s ![jL, jL'])`. Establish `u2` using `valF_mul_inv _ a2 (Q.L.rig.s fun _ => jL')`. Establish `key : e ^ (n ^ 2) = valF (x' ≫ Q.φ) _ (κ.s ![jL, jL']).val * valF M.pt _ (Q.L.rig.s fun _ => jL').val`.

Rewrite using `[he, div_pow, div_eq_iff (pow_ne_zero _ u3), hF, ← hx2, E2, ← _root_.mul_assoc, E1]`. Expand and normalize the polynomial expressions, which then agree. Establish `k3 : e ^ (n ^ 2) * (valF (x' ≫ Q.φ) _ (κ.s ![jL, jL'])⁻¹.val * valF M.pt _ (Q.L.rig.s fun _ => jL')⁻¹.val) = 1`. Rewrite using `[key, _root_.mul_mul_mul_comm]`. Conclude with `(congrArg₂ (· * ·) u1 u2).trans (_root_.mul_one 1)`.

Use `⟨fun h0 => ?_, mem_O_of_pow hO.normal npos ?_, mem_O_of_pow hO.normal npos ?_⟩` and prove the remaining obligations. Rewrite `k3` using `[h0, zero_pow npos.ne', zero_mul]`. Conclude with `zero_ne_one k3`. Rewrite using `[key]`. Conclude with `mul_mem (b1 _) (b2 _)`.

Rewrite using `[inv_pow, ← eq_inv_of_mul_eq_one_right k3]`. Conclude with `mul_mem (b1 _) (b2 _)`.
-/
theorem frameUnit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → (∀ (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A (S.r * S.N)).left] ![(((S.r * S.N) : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig (S.r * S.N) α → ∃ κ, κ.IsGen ∧ Q.MulRel (S.r * S.N) α κ) → ∀ (a : S.Gam) (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.left) (w : W.toScheme), Q.ExtPt a W h → Q.FrameUnit a W h w := by
  intro o Ω _ _ _ _ S ρ M U₀ Q hO hκ a W h w hE jP jL x' e hw hx1 hx2 hjP he
  obtain ⟨hpn, -, α, hα, hN, hc⟩ := ρ.fr_tors a
  obtain ⟨κ, -, hR⟩ := hκ α hα hN
  have npos : 0 < (S.r * S.N) ^ 2 := pow_pos (Nat.mul_pos S.r_pos (lt_of_lt_of_le two_pos S.N_ge)) 2
  generalize S.r * S.N = n at hpn α hα hN hc κ hR npos
  clear hκ
  set y : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom with hy
  obtain ⟨jP', hjP', hF⟩ := frame_val ρ.P ρ.rig n (ρ.pt a) hpn (ρ.fr a) α hc y jP (hx2 ▸ hjP)
  have hWne : (W : Set M.Z).Nonempty := ⟨w.1, w.2⟩
  let x : Sp Ω ⟶ W.toScheme := IsOpenImmersion.lift W.ι M.pt (by
    rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hWne))
  have hx : x ≫ W.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxh : x ≫ h = x' ≫ Q.φ := hE.2 x x' hx hx1 hx2
  have s1 : (x' ≫ pullback.snd _ _) ≫ U₀.ι = M.pt := by
    rw [← hx1, Q.cart.1.w]; exact Category.assoc _ _ _
  have s2 : (x' ≫ pullback.snd _ _) ≫ Q.u₀ = y := Q.u₀_gen _ s1
  have hb := isGrpPullback_pullback ρ.P.A Q.u₀
  let g' : Sp Ω ⟶ pullback ρ.P.A.hom Q.u₀ := x' ≫ (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n).left
  have g1 : g' ≫ pullback.fst _ _ = x' ≫ pullback.fst _ _ ≫ (mulA ρ.P.A n).left :=
    (Category.assoc _ _ _).trans (congrArg (x' ≫ ·) (mulA_comm hb n))
  have g2 : g' ≫ pullback.snd _ _ = x' ≫ pullback.snd _ _ :=
    (Category.assoc _ _ _).trans (congrArg (x' ≫ ·) (Over.w (mulA ((Over.pullback Q.u₀).obj ρ.P.A) n)))
  have g3 : g' ≫ pullback.fst _ _ = y ≫ eSec ρ.P.A := by
    rw [g1, ← Category.assoc, hx2, Category.assoc]
    refine congrArg (y ≫ ·) ((comp_mulA _ n).trans ?_)
    rw [hpn, one_left]; exact Category.id_comp _
  have g4 : g' = (x' ≫ pullback.snd _ _) ≫ eSec ((Over.pullback Q.u₀).obj ρ.P.A) := by
    apply pullback.hom_ext
    · rw [g3, ← s2]
      exact (Category.assoc _ _ _).trans ((congrArg ((x' ≫ pullback.snd _ _) ≫ ·) (eSec_comm hb).symm).trans
        (Category.assoc _ _ _).symm)
    · rw [g2]
      exact (Category.comp_id _).symm.trans ((congrArg ((x' ≫ pullback.snd _ _) ≫ ·)
        (Over.w η[(Over.pullback Q.u₀).obj ρ.P.A]).symm).trans (Category.assoc _ _ _).symm)
  have g5 : g' ≫ Q.φ = M.pt ≫ eSec Q.G := by
    have e1 := eSec_comm Q.cart
    rw [g4, ← s1]
    exact (Category.assoc _ _ _).trans ((congrArg ((x' ≫ pullback.snd _ _) ≫ ·) e1).trans
        (Category.assoc _ _ _).symm)
  have g6 : g' ≫ Q.φ = x' ≫ Q.φ ≫ (mulA Q.G n).left :=
    (Category.assoc _ _ _).trans (congrArg (x' ≫ ·) (mulA_comm Q.cart n))
  have hdom : IsDominant x := by
    have : IsDominant (x ≫ W.ι) := hx ▸ M.isDominant_pt
    exact ⟨W.ι.isOpenEmbedding.isInducing.dense_iff.2 fun p => by
      rw [← Set.range_comp]; exact this.1 _⟩
  have hsep : IsSeparated Q.G.hom := Q.semi.separated
  have hmul : h ≫ (mulA Q.G n).left = W.ι ≫ eSec Q.G := by
    refine ext_of_isDominant_of_isSeparated Q.G.hom ?_ x ?_
    · rw [Category.assoc, Over.w, hE.1, Category.assoc]
      exact ((congrArg (W.ι ≫ ·) (Over.w η[Q.G])).trans (Category.comp_id _)).symm
    · rw [← Category.assoc, hxh, Category.assoc, ← g6, g5, ← hx, Category.assoc]
  obtain ⟨jL', hjL'⟩ : ∃ j, eSec Q.G (W.ι w) ∈ Q.L.L.U j :=
    TopologicalSpace.Opens.mem_iSup.1 (Q.L.isLB.cover.ge trivial)
  have k1 : h w ∈ LB.wchart Q.L.L ![𝟙 Q.G.left, (mulA Q.G n).left] ![jL, jL'] := Set.mem_iInter.2 fun k => by
    fin_cases k
    · exact hw
    · show (h ≫ (mulA Q.G n).left) w ∈ Q.L.L.U jL'
      rw [hmul]; exact hjL'
  have k2 : W.ι w ∈ LB.wchart Q.L.L (fun _ : PUnit => eSec Q.G) (fun _ => jL') := Set.mem_iInter.2 fun _ => hjL'
  obtain ⟨a1, b1⟩ := valF_comp_mem h x hx w k1
  obtain ⟨a2, b2⟩ := valF_comp_mem W.ι x hx w k2
  rw [hxh] at a1 b1
  rw [hx] at a2 b2
  have r1 : Set.range (x' ≫ Q.φ) ⊆ Q.L.L.U jL := by
    rintro _ ⟨p, rfl⟩; exact Set.mem_iInter.1 (a1 (x := p) trivial) 0
  have r2 : Set.range (g' ≫ Q.φ) ⊆ Q.L.L.U jL' := by
    rw [g5]; rintro _ ⟨p, rfl⟩; exact Set.mem_iInter.1 (a2 (x := p) trivial) PUnit.unit
  have r3 : Set.range (g' ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP' := g3 ▸ hjP'
  have E1 := hR Ω x' g' jP jP' jL jL' g1 g2 hjP r1 r3 r2
  have E2 := Q.w_rig Ω g' M.pt y jP' jL' g5 g3 r3 r2
  have a3 : ⊤ ≤ x' ⁻¹ᵁ (LB.div (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) (Q.L.L.pull Q.φ)).U
      (fun _ => jP, fun _ => jL) := fun p _ =>
    ⟨Set.mem_iInter.2 fun _ => hjP ⟨p, rfl⟩, Set.mem_iInter.2 fun _ => r1 ⟨p, rfl⟩⟩
  have u3 := left_ne_zero_of_mul_eq_one (valF_mul_inv x' a3 (Q.w.s (fun _ => jP, fun _ => jL)))
  have u1 := valF_mul_inv _ a1 (κ.s ![jL, jL'])
  have u2 := valF_mul_inv _ a2 (Q.L.rig.s fun _ => jL')
  have key : e ^ (n ^ 2) = valF (x' ≫ Q.φ) _ (κ.s ![jL, jL']).val * valF M.pt _ (Q.L.rig.s fun _ => jL').val := by
    rw [he, div_pow, div_eq_iff (pow_ne_zero _ u3), hF, ← hx2, E2, ← _root_.mul_assoc, E1]
    ring
  have k3 : e ^ (n ^ 2) * (valF (x' ≫ Q.φ) _ (κ.s ![jL, jL'])⁻¹.val *
      valF M.pt _ (Q.L.rig.s fun _ => jL')⁻¹.val) = 1 := by
    rw [key, _root_.mul_mul_mul_comm]
    exact (congrArg₂ (· * ·) u1 u2).trans (_root_.mul_one 1)
  refine ⟨fun h0 => ?_, mem_O_of_pow hO.normal npos ?_, mem_O_of_pow hO.normal npos ?_⟩
  · rw [h0, zero_pow npos.ne', zero_mul] at k3
    exact zero_ne_one k3
  · rw [key]; exact mul_mem (b1 _) (b2 _)
  · rw [inv_pow, ← eq_inv_of_mul_eq_one_right k3]; exact mul_mem (b1 _) (b2 _)

end GlobalTheory.ZH.TorsFrame
end
