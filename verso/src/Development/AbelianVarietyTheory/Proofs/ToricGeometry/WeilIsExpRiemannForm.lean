import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.WeilExp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h k t _`. Conclude with `Set.mem_iInter.1 (h (Set.mem_univ t)) k`. Introduce `h t _`. Conclude with `Set.mem_iInter.2 fun k => h k (Set.mem_univ t)`.
-/
theorem le_wchart_iff {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (j : K → L.ι)
    (x : Z ⟶ Y) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  constructor
  · intro h k t _
    exact Set.mem_iInter.1 (h (Set.mem_univ t)) k
  · intro h t _
    exact Set.mem_iInter.2 fun k => h k (Set.mem_univ t)

section Transl

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

/- English proof (translation)
Rewrite using `[← Over.comp_left, Out.translT, lift_snd]`.
-/
theorem translT_snd (x : T ⟶ A) :
    (Out.translT A x).left ≫ (snd T A).left = (Out.translPt A x).left := by
  rw [← Over.comp_left, Out.translT, lift_snd]

/- English proof (translation)
Rewrite using `[← Over.comp_left, ← Over.comp_left]`. Use `congr 1`. Use `show Out.translT A x ≫ ((fst T A ≫ y) * snd T A) = Out.translT A y ≫ ((fst T A ≫ x) * snd T A)`. Rewrite using `[MonObj.comp_mul, MonObj.comp_mul, Out.translT, Out.translT, lift_snd, lift_snd, ← Category.assoc, ← Category.assoc, lift_fst, lift_fst]`. Conclude with `mul_left_comm _ _ _`.
-/
theorem translT_translPt_comm [IsCommMonObj A] (x y : T ⟶ A) :
    (Out.translT A x).left ≫ (Out.translPt A y).left = (Out.translT A y).left ≫ (Out.translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show Out.translT A x ≫ ((fst T A ≫ y) * snd T A) = Out.translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, Out.translT, Out.translT, lift_snd, lift_snd, ← Category.assoc,
    ← Category.assoc, lift_fst, lift_fst]
  exact mul_left_comm _ _ _

/- English proof (translation)
Use `show lift p q ≫ ((fst T A ≫ x) * snd T A) = _`. Rewrite using `[MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]`.
-/
theorem lift_translPt {W : Over S} (p : W ⟶ T) (q : W ⟶ A) (x : T ⟶ A) :
    lift p q ≫ Out.translPt A x = (p ≫ x) * q := by
  show lift p q ≫ ((fst T A ≫ x) * snd T A) = _
  rw [MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst]

/- English proof (translation)
Rewrite using `[Out.translT, comp_lift, lift_fst, lift_translPt]`.
-/
theorem lift_translT {W : Over S} (p : W ⟶ T) (q : W ⟶ A) (x : T ⟶ A) :
    lift p q ≫ Out.translT A x = lift p ((p ≫ x) * q) := by
  rw [Out.translT, comp_lift, lift_fst, lift_translPt]

end Transl

/- English proof (translation)
Establish `h1 : b ⬝ᵥ Hm.mulVec (star a) = star (a ⬝ᵥ Hm.mulVec (star b))`. Rewrite using `[← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]`. Establish `h2 : (E : ℂ) = ((a ⬝ᵥ Hm.mulVec (star b)).im : ℂ)`. Rewrite using `[← hE]`. Simplify using the standard rewrite rules.

Establish `h3` using `Complex.sub_conj (a ⬝ᵥ Hm.mulVec (star b))`. Rewrite using `[← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, h1, h2]`. Use `congr 1`. Rewrite using `[Complex.star_def]`. Simplify using `only [smul_eq_mul]`.

Move the coercions through the operations in `at h3`. Take the linear combination `(-(Real.pi : ℂ) * (k : ℂ)⁻¹) * h3`.
-/
theorem exp_comm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian) (k : ℕ) (a b z : Fin g → ℂ) (E : ℤ)
    (hE : (E : ℝ) = (a ⬝ᵥ Hm.mulVec (star b)).im) :
    cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star a)))) *
        cexp (-(Real.pi * ((z + (k : ℂ)⁻¹ • a) ⬝ᵥ Hm.mulVec (star b)))) =
      cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star b)))) *
        cexp (-(Real.pi * ((z + (k : ℂ)⁻¹ • b) ⬝ᵥ Hm.mulVec (star a)))) *
        cexp (-(2 * Real.pi * Complex.I) * (E : ℂ) / k) := by
  have h1 : b ⬝ᵥ Hm.mulVec (star a) = star (a ⬝ᵥ Hm.mulVec (star b)) := by
    rw [← star_dotProduct_star, star_mulVec, star_star, hH.eq, dotProduct_mulVec]
  have h2 : (E : ℂ) = ((a ⬝ᵥ Hm.mulVec (star b)).im : ℂ) := by
    rw [← hE]; simp
  have h3 := Complex.sub_conj (a ⬝ᵥ Hm.mulVec (star b))
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, add_dotProduct, add_dotProduct,
    smul_dotProduct, smul_dotProduct, h1, h2]
  congr 1
  rw [Complex.star_def]
  simp only [smul_eq_mul]
  push_cast at h3
  linear_combination (-(Real.pi : ℂ) * (k : ℂ)⁻¹) * h3

/- English proof (translation)
Establish `h₅ : A₁ * A₂ * Fab = Ca * Cb * (e₁ * e₂) * F₀`. Apply `mul_right_cancel₀ ha` to reduce the goal to its premises. Take the linear combination `(A₂ * Fab) * h₁ + (Ca * e₁ * F₀) * h₂`. Establish `h₆ : B₁ * B₂ * Fab = Ca * Cb * (e₃ * e₄) * F₀`. Apply `mul_right_cancel₀ hb` to reduce the goal to its premises.

Take the linear combination `(B₂ * Fab) * h₃ + (Cb * e₃ * F₀) * h₄`. Apply `mul_right_cancel₀ hab` to reduce the goal to its premises. Rewrite using `[h₅, he]`. Take the linear combination `(-c) * h₆`.
-/
theorem cancel_frames {A₁ A₂ B₁ B₂ F₀ Fa Fb Fab Ca Cb e₁ e₂ e₃ e₄ c : ℂ} (ha : Fa ≠ 0) (hb : Fb ≠ 0)
    (hab : Fab ≠ 0) (h₁ : A₁ * Fa = Ca * e₁ * F₀) (h₂ : A₂ * Fab = Cb * e₂ * Fa)
    (h₃ : B₁ * Fb = Cb * e₃ * F₀) (h₄ : B₂ * Fab = Ca * e₄ * Fb) (he : e₁ * e₂ = e₃ * e₄ * c) :
    A₁ * A₂ = B₁ * B₂ * c := by
  have h₅ : A₁ * A₂ * Fab = Ca * Cb * (e₁ * e₂) * F₀ := by
    apply mul_right_cancel₀ ha
    linear_combination (A₂ * Fab) * h₁ + (Ca * e₁ * F₀) * h₂
  have h₆ : B₁ * B₂ * Fab = Ca * Cb * (e₃ * e₄) * F₀ := by
    apply mul_right_cancel₀ hb
    linear_combination (B₂ * Fab) * h₃ + (Cb * e₃ * F₀) * h₄
  apply mul_right_cancel₀ hab
  rw [h₅, he]
  linear_combination (-c) * h₆

section Values

variable (hv : ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a))
include hv

/- English proof (translation)
The claim follows from `(hv X x).2.2.1 U V h f.val hx`.
-/
theorem val_res {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)ˣ) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    valAt' x V (res h f).val = valAt' x U f.val :=
  (hv X x).2.2.1 U V h f.val hx

/- English proof (translation)
Take `⟨e, he⟩` from `(hv X x).2.1 U hx`. Rewrite using `[he, he, he, Units.val_mul, map_mul]`.
-/
theorem val_mul {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {U : X.Opens} (f f' : Γ(X, U)ˣ) (hx : ⊤ ≤ x ⁻¹ᵁ U) :
    valAt' x U (f * f').val = valAt' x U f.val * valAt' x U f'.val := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U hx
  rw [he, he, he, Units.val_mul, map_mul]

/- English proof (translation)
The claim follows from `(hv X x).2.2.2.1 Y φ U f.val`.
-/
theorem val_pull {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)ˣ) :
    valAt' x (φ ⁻¹ᵁ U) (pullU φ U f).val = valAt' (x ≫ φ) U f.val :=
  (hv X x).2.2.2.1 Y φ U f.val

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']

/- English proof (translation)
The claim follows from `(val_mul hv x _ _ hx).trans (congrArg₂ (· * ·) (val_res hv x _ _ hx) (val_res hv x _ _ hx))`.
-/
theorem val_mulGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (j : K ⊕ K' → L.ι) (x : Sp ℂ ⟶ Y)
    (hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (Sum.elim φ φ') j) :
    valAt' x (LB.wchart L (Sum.elim φ φ') j) ((LB.mulGen L φ ε φ' ε' t t').s j).val =
      valAt' x (LB.wchart L φ (j ∘ Sum.inl)) (t.s (j ∘ Sum.inl)).val *
        valAt' x (LB.wchart L φ' (j ∘ Sum.inr)) (t'.s (j ∘ Sum.inr)).val :=
  (val_mul hv x _ _ hx).trans (congrArg₂ (· * ·) (val_res hv x _ _ hx) (val_res hv x _ _ hx))

/- English proof (translation)
The claim follows from `(val_res hv x _ _ hx).trans (val_pull hv x h _ _)`.
-/
theorem val_pullGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y) (j : K → L.ι)
    (x : Sp ℂ ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ k) j) :
    valAt' x (LB.wchart L (fun k => h ≫ φ k) j) ((LB.pullGen L φ ε t h).s j).val =
      valAt' (x ≫ h) (LB.wchart L φ j) (t.s j).val :=
  (val_res hv x _ _ hx).trans (val_pull hv x h _ _)

/- English proof (translation)
Establish `hx : ⊤ ≤ x.left ⁻¹ᵁ LB.wchart M (Y` using `(Out.overRes V ⊗ A).left) (K := PEmpty) PEmpty.elim j := (le_wchart_iff _ _ _ _).2 fun k => k.elim`. Use `(val_res hv x.left _ _ hx).trans ?_` and prove the remaining obligations. Use `(val_pull hv x.left (fst (Out.overRes V) A).left ⊤ _).trans ?_` and prove the remaining obligations. Use `(val_pull hv _ V.ι ⊤ (unitOn c)).trans ?_` and prove the remaining obligations. Establish `e : (x.left ≫ (fst (Out.overRes V) A).left) ≫ V.ι = 𝟙 (Sp ℂ)`.

Establish `: (x ≫ fst (Out.overRes V) A) ≫ Out.overResι V = 𝟙 _` using `Subsingleton.elim _ _`. Conclude with `congrArg (·.left) this`. Rewrite using `[e]`. Use `(hv _ (𝟙 (Sp ℂ))).2.2.2.2.2 (𝟙 _) (Category.id_comp _) ⊤ c le_top` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations.

Use `congr 1`.
-/
theorem val_constGen {A : Over (Sp ℂ)} [GrpObj A] (M : LB A.left) (V : (𝟙_ (Over (Sp ℂ))).left.Opens) (c : ℂˣ)
    (x : 𝟙_ (Over (Sp ℂ)) ⟶ Out.overRes V ⊗ A) (j : PEmpty → M.ι) :
    valAt' x.left _ ((Out.constGen A M (Out.unitRes V (unitOn c))).s j).val = c := by
  have hx : ⊤ ≤ x.left ⁻¹ᵁ LB.wchart M (Y := (Out.overRes V ⊗ A).left) (K := PEmpty) PEmpty.elim j :=
    (le_wchart_iff _ _ _ _).2 fun k => k.elim
  refine (val_res hv x.left _ _ hx).trans ?_
  refine (val_pull hv x.left (fst (Out.overRes V) A).left ⊤ _).trans ?_
  refine (val_pull hv _ V.ι ⊤ (unitOn c)).trans ?_
  have e : (x.left ≫ (fst (Out.overRes V) A).left) ≫ V.ι = 𝟙 (Sp ℂ) := by
    have : (x ≫ fst (Out.overRes V) A) ≫ Out.overResι V = 𝟙 _ := Subsingleton.elim _ _
    exact congrArg (·.left) this
  rw [e]
  have := (hv _ (𝟙 (Sp ℂ))).2.2.2.2.2 (𝟙 _) (Category.id_comp _) ⊤ c le_top
  refine Eq.trans ?_ this
  congr 1

end Values

/- English proof (translation)
Introduce `hW hv hext hred hth P u Hm χ Ef hAH k a b c hk hc p₀`. Use `P.isAb.comm` as an intermediate fact. Use `P.isAb.smooth` as an intermediate fact. Establish `hk0 : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Establish `hex0 : u.ex 0 = 1` using `(u.ker 0).2 u.Λ.zero_mem`.

Establish `hpow : ∀ (n : ℕ) w, u.ex w ^ n = u.ex ((n : ℂ) • w)`. Introduce `n w`. Proceed by induction on `n with`. Consider the case `zero => simp [hex0]`. Consider the case `succ n ih => rw [pow_succ, ih, ← u.ex_add, Nat.cast_succ, add_smul, one_smul]`.

Establish `htor : ∀ l : u.Λ, u.ex ((k : ℂ)⁻¹ • (l : Fin P.g → ℂ)) ^ k = 1`. Introduce `l`. Rewrite using `[hpow, smul_smul, mul_inv_cancel₀ hk0, one_smul]`. Conclude with `(u.ker _).2 l.2`. Take `⟨c', hc', -⟩` from `(hW (Sp ℂ) P k (𝟙_ _)).1 _ _ (htor a) (htor b)`.

Take `⟨V, hV, hl, -⟩` from `hc' p₀`. Use `⟨V, hV, hl, fun θx θy hx hy => ?_⟩` and prove the remaining obligations. Introduce `j j' _ _ hjj`. Establish `hsm : Smooth (Out.overRes V ⊗ P.A).hom`. Rewrite using `[← Over.w (fst (Out.overRes V) P.A)]`.

Establish `h1 : Smooth (fst (Out.overRes V) P.A).left` using `by show Smooth (pullback.fst (Out.overRes V).hom P.A.hom) infer_instance`. Establish `h2 : Smooth (Out.overRes V).hom` using `by show Smooth (V.ι ≫ 𝟙 _) infer_instance`. Use `infer_instance`. Apply `Units.ext` to reduce the goal to its premises. Use `hext (Out.overRes V ⊗ P.A) (hred _ _ hsm) inferInstance _ _ _ fun x hxU => ?_` and prove the remaining obligations.

Establish `hxj` using `hxU.trans (x.left.preimage_mono inf_le_left)`. Establish `hxj'` using `hxU.trans (x.left.preimage_mono inf_le_right)`. Use `(val_res hv _ _ _ hxU).trans (Eq.trans ?_ (val_res hv _ _ _ hxU).symm)` and prove the remaining obligations. Take `⟨z, hz⟩` from `u.ex_onto (x ≫ snd _ _)`. Apply the tactic sequence `obtain ⟨p, rfl⟩ : ∃ p, x = lift p (u.ex z) := ⟨x ≫ fst _ _, by rw [hz]; ext <;> simp⟩`.

Establish `hp : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, p ≫ Out.overResι V ≫ y = y`. Introduce `y`. Rewrite using `[← Category.assoc, Subsingleton.elim (p ≫ Out.overResι V) (𝟙 _), Category.id_comp]`. Establish `hpx : p ≫ θx.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))` using `by rw [hx, hp]`. Establish `hpy : p ≫ θy.pt = u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))` using `by rw [hy, hp]`.

Take `⟨Ca, hCa⟩` from `hth P u Hm χ Ef hAH k a hk _ p θx hpx`. Take `⟨Cb, hCb⟩` from `hth P u Hm χ Ef hAH k b hk _ p θy hpy`. Establish `tr : ∀ (θ : Out.ThetaGrp P.A P.L k (Out.overRes V)) (v : Fin P.g → ℂ), p ≫ θ.pt = u.ex v → ∀ w, (lift p (u.ex w)).left ≫ (Out.translT P.A θ.pt).left = (lift p (u.ex (w + v))).left ∧ (lift p (u.ex w)).left ≫ (Out.translPt P.A θ.pt).left = (u.ex (w + v)).left`. Introduce `θ v h w`. Rewrite using `[← Over.comp_left, ← Over.comp_left, lift_translT, lift_translPt, h, ← u.ex_add, add_comm v w]`.

Conclude with `⟨rfl, rfl⟩`. Establish `sn : ∀ w, (lift p (u.ex w)).left ≫ (snd (Out.overRes V) P.A).left = (u.ex w).left`. Introduce `w`. Rewrite using `[← Over.comp_left, lift_snd]`. Establish `m` using `(le_wchart_iff _ _ _ _).1 hxj`.

Establish `m'` using `(le_wchart_iff _ _ _ _).1 hxj'`. Establish `m₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j (.inl 0))`. Rewrite using `[← sn]`. Conclude with `m (.inl 0)`. Establish `m₂ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j (.inl 1))`.

Rewrite using `[← (tr θx _ hpx z).2]`. Conclude with `m (.inl 1)`. Establish `m₃ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j' (.inl (.inl 1)))`. Rewrite using `[← (tr θy _ hpy z).2]`. Conclude with `m' (.inl (.inl 1))`.

Establish `m₄ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j (.inr 1))`. Rewrite using `[← (tr θy _ hpy _).2, ← (tr θx _ hpx z).1, Category.assoc]`. Conclude with `m (.inr 1)`. Establish `e₁ : j (.inl 0) = j' (.inl (.inl 0))` using `hjj _ _ rfl`. Establish `e₂ : j (.inl 1) = j (.inr 0)` using `‹LB.Coh P.L _ j› _ _ (translT_snd θx.pt).symm`.

Establish `e₃ : j' (.inl (.inl 1)) = j' (.inl (.inr 0))` using `‹LB.Coh P.L _ j'› _ _ (translT_snd θy.pt).symm`. Establish `e₄ : j (.inr 1) = j' (.inl (.inr 1))` using `hjj _ _ (translT_translPt_comm θx.pt θy.pt)`. Establish `ec : z + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) = z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ)` using `add_right_comm _ _ _`. Establish `h₁` using `hCa (j ∘ Sum.inl) z m₁ m₂`. Establish `h₂` using `hCb (j ∘ Sum.inr) _ (e₂ ▸ m₂ :) m₄`.

Establish `h₃` using `hCb ((j' ∘ Sum.inl) ∘ Sum.inl) z (e₁ ▸ m₁ :) m₃`. Establish `h₄` using `hCa ((j' ∘ Sum.inl) ∘ Sum.inr) _ (e₃ ▸ m₃ :) (by rw [ec]; exact (e₄ ▸ m₄ :))`. Simplify using `only [Function.comp_apply] at h₁ h₂ h₃ h₄`. Rewrite `h₂` using `[← e₂]`. Rewrite `h₃` using `[← e₁]`.

Rewrite `h₄` using `[← e₃, ← e₄, ec]`. Establish `key` using `cancel_frames (pow_ne_zero k (u.fr_ne _ _ m₂)) (pow_ne_zero k (u.fr_ne _ _ m₃)) (pow_ne_zero k (u.fr_ne _ _ m₄)) h₁ h₂ h₃ h₄ (by rw [hc]; exact exp_comm Hm hAH.1 k a b z (Ef a b) (hAH.2.2.1 a b) : _ = _ * _ * (c : ℂ))`. Establish `n₁` using `(le_wchart_iff _ _ (j ∘ Sum.inr) _).2 fun i => m (.inr i)`. Establish `n₂` using `(le_wchart_iff _ _ (j' ∘ Sum.inl) _).2 fun i => m' (.inl i)`. Establish `n₃` using `(le_wchart_iff _ _ ((j' ∘ Sum.inl) ∘ Sum.inr) _).2 fun i => m' (.inl (.inr i))`.

Use `(val_mulGen hv _ _ _ _ _ _ _ _ _ hxj).trans (Eq.trans ?_ (val_mulGen hv _ _ _ _ _ _ _ _ _ hxj').symm)` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg₂ (· * ·) (val_mulGen hv _ _ _ _ _ _ _ _ _ n₂) (val_constGen hv P.L V c _ _)).symm` and prove the remaining obligations. Use `(congrArg (_ * ·) (val_pullGen hv _ _ _ _ _ _ _ n₁)).trans (Eq.trans ?_ (congrArg (_ * · * (c : ℂ)) (val_pullGen hv _ _ _ _ _ _ _ n₃).symm))` and prove the remaining obligations. Rewrite using `[(tr θx _ hpx z).1, (tr θy _ hpy z).1]`. Conclude with `key`.
-/
theorem weilIs_exp_riemannForm : Out.WeilSt → (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') → (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a : u.Λ), 0 < k → ∀ (T : Over (Sp ℂ)) (p : (𝟙_ (Over (Sp ℂ)) ⟶ T)) (θ : Out.ThetaGrp P.A P.L k T), p ≫ θ.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) → ∃ C : ℂ, ∀ (j : Fin 2 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j 1) → valAt' (lift p (u.ex z)).left _ (θ.φ.s j).val * u.fr (j 1) (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ^ k = C * cexp (-(Real.pi * (z ⬝ᵥ Hm.mulVec (star (a : Fin P.g → ℂ))))) * u.fr (j 0) z ^ k) → (∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), (Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin P.g → ℂ))))) * u.fr i (z + l)) → ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c)) := by
  intro hW hv hext hred hth P u Hm χ Ef hAH k a b c hk hc p₀
  have := P.isAb.comm
  have := P.isAb.smooth
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hex0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  have hpow : ∀ (n : ℕ) w, u.ex w ^ n = u.ex ((n : ℂ) • w) := by
    intro n w
    induction n with
    | zero => simp [hex0]
    | succ n ih => rw [pow_succ, ih, ← u.ex_add, Nat.cast_succ, add_smul, one_smul]
  have htor : ∀ l : u.Λ, u.ex ((k : ℂ)⁻¹ • (l : Fin P.g → ℂ)) ^ k = 1 := by
    intro l
    rw [hpow, smul_smul, mul_inv_cancel₀ hk0, one_smul]
    exact (u.ker _).2 l.2
  obtain ⟨c', hc', -⟩ := (hW (Sp ℂ) P k (𝟙_ _)).1 _ _ (htor a) (htor b)
  obtain ⟨V, hV, hl, -⟩ := hc' p₀
  refine ⟨V, hV, hl, fun θx θy hx hy => ?_⟩
  intro j j' _ _ hjj
  have hsm : Smooth (Out.overRes V ⊗ P.A).hom := by
    rw [← Over.w (fst (Out.overRes V) P.A)]
    have h1 : Smooth (fst (Out.overRes V) P.A).left := by
      show Smooth (pullback.fst (Out.overRes V).hom P.A.hom)
      infer_instance
    have h2 : Smooth (Out.overRes V).hom := by
      show Smooth (V.ι ≫ 𝟙 _)
      infer_instance
    infer_instance
  apply Units.ext
  refine hext (Out.overRes V ⊗ P.A) (hred _ _ hsm) inferInstance _ _ _ fun x hxU => ?_
  have hxj := hxU.trans (x.left.preimage_mono inf_le_left)
  have hxj' := hxU.trans (x.left.preimage_mono inf_le_right)
  refine (val_res hv _ _ _ hxU).trans (Eq.trans ?_ (val_res hv _ _ _ hxU).symm)
  obtain ⟨z, hz⟩ := u.ex_onto (x ≫ snd _ _)
  obtain ⟨p, rfl⟩ : ∃ p, x = lift p (u.ex z) := ⟨x ≫ fst _ _, by rw [hz]; ext <;> simp⟩
  have hp : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, p ≫ Out.overResι V ≫ y = y := by
    intro y
    rw [← Category.assoc, Subsingleton.elim (p ≫ Out.overResι V) (𝟙 _), Category.id_comp]
  have hpx : p ≫ θx.pt = u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ)) := by rw [hx, hp]
  have hpy : p ≫ θy.pt = u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ)) := by rw [hy, hp]
  obtain ⟨Ca, hCa⟩ := hth P u Hm χ Ef hAH k a hk _ p θx hpx
  obtain ⟨Cb, hCb⟩ := hth P u Hm χ Ef hAH k b hk _ p θy hpy

  have tr : ∀ (θ : Out.ThetaGrp P.A P.L k (Out.overRes V)) (v : Fin P.g → ℂ), p ≫ θ.pt = u.ex v → ∀ w,
      (lift p (u.ex w)).left ≫ (Out.translT P.A θ.pt).left = (lift p (u.ex (w + v))).left ∧
      (lift p (u.ex w)).left ≫ (Out.translPt P.A θ.pt).left = (u.ex (w + v)).left := by
    intro θ v h w
    rw [← Over.comp_left, ← Over.comp_left, lift_translT, lift_translPt, h, ← u.ex_add, add_comm v w]
    exact ⟨rfl, rfl⟩
  have sn : ∀ w, (lift p (u.ex w)).left ≫ (snd (Out.overRes V) P.A).left = (u.ex w).left := by
    intro w
    rw [← Over.comp_left, lift_snd]
  have m := (le_wchart_iff _ _ _ _).1 hxj
  have m' := (le_wchart_iff _ _ _ _).1 hxj'
  have m₁ : ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j (.inl 0)) := by
    rw [← sn]; exact m (.inl 0)
  have m₂ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j (.inl 1)) := by
    rw [← (tr θx _ hpx z).2]; exact m (.inl 1)
  have m₃ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ))).left ⁻¹ᵁ P.L.U (j' (.inl (.inl 1))) := by
    rw [← (tr θy _ hpy z).2]; exact m' (.inl (.inl 1))
  have m₄ : ⊤ ≤ (u.ex (z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ))).left ⁻¹ᵁ
      P.L.U (j (.inr 1)) := by
    rw [← (tr θy _ hpy _).2, ← (tr θx _ hpx z).1, Category.assoc]; exact m (.inr 1)
  have e₁ : j (.inl 0) = j' (.inl (.inl 0)) := hjj _ _ rfl
  have e₂ : j (.inl 1) = j (.inr 0) := ‹LB.Coh P.L _ j› _ _ (translT_snd θx.pt).symm
  have e₃ : j' (.inl (.inl 1)) = j' (.inl (.inr 0)) := ‹LB.Coh P.L _ j'› _ _ (translT_snd θy.pt).symm
  have e₄ : j (.inr 1) = j' (.inl (.inr 1)) := hjj _ _ (translT_translPt_comm θx.pt θy.pt)
  have ec : z + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) =
      z + (k : ℂ)⁻¹ • (a : Fin P.g → ℂ) + (k : ℂ)⁻¹ • (b : Fin P.g → ℂ) := add_right_comm _ _ _
  have h₁ := hCa (j ∘ Sum.inl) z m₁ m₂
  have h₂ := hCb (j ∘ Sum.inr) _ (e₂ ▸ m₂ :) m₄
  have h₃ := hCb ((j' ∘ Sum.inl) ∘ Sum.inl) z (e₁ ▸ m₁ :) m₃
  have h₄ := hCa ((j' ∘ Sum.inl) ∘ Sum.inr) _ (e₃ ▸ m₃ :) (by rw [ec]; exact (e₄ ▸ m₄ :))
  simp only [Function.comp_apply] at h₁ h₂ h₃ h₄
  rw [← e₂] at h₂
  rw [← e₁] at h₃
  rw [← e₃, ← e₄, ec] at h₄
  have key := cancel_frames (pow_ne_zero k (u.fr_ne _ _ m₂)) (pow_ne_zero k (u.fr_ne _ _ m₃))
    (pow_ne_zero k (u.fr_ne _ _ m₄)) h₁ h₂ h₃ h₄
    (by rw [hc]; exact exp_comm Hm hAH.1 k a b z (Ef a b) (hAH.2.2.1 a b) : _ = _ * _ * (c : ℂ))
  have n₁ := (le_wchart_iff _ _ (j ∘ Sum.inr) _).2 fun i => m (.inr i)
  have n₂ := (le_wchart_iff _ _ (j' ∘ Sum.inl) _).2 fun i => m' (.inl i)
  have n₃ := (le_wchart_iff _ _ ((j' ∘ Sum.inl) ∘ Sum.inr) _).2 fun i => m' (.inl (.inr i))
  refine (val_mulGen hv _ _ _ _ _ _ _ _ _ hxj).trans (Eq.trans ?_ (val_mulGen hv _ _ _ _ _ _ _ _ _ hxj').symm)
  refine Eq.trans ?_ (congrArg₂ (· * ·) (val_mulGen hv _ _ _ _ _ _ _ _ _ n₂)
    (val_constGen hv P.L V c _ _)).symm
  refine (congrArg (_ * ·) (val_pullGen hv _ _ _ _ _ _ _ n₁)).trans
    (Eq.trans ?_ (congrArg (_ * · * (c : ℂ)) (val_pullGen hv _ _ _ _ _ _ _ n₃).symm))
  rw [(tr θx _ hpx z).1, (tr θy _ hpy z).1]
  exact key

end GlobalTheory.WeilExp
