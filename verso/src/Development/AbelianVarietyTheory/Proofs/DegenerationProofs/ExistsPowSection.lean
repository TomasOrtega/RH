import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SecPow
variable {X X' : Scheme.{0}}

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ (t + e), ih]`. Use `push_cast`.

Take the linear combination `((m : R) + 1) * t ^ m * he`.
-/
theorem add_pow_succ_of_mul_self {R : Type} [CommRing R] (t e : R) (he : e * e = 0) (m : ℕ) :
    (t + e) ^ (m + 1) = t ^ (m + 1) + ((m + 1 : ℕ) : R) * (t ^ m * e) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (t + e), ih]
    push_cast
    linear_combination ((m : R) + 1) * t ^ m * he

/- English proof (translation)
Use extensionality with `x`. Take `⟨y, rfl⟩` from `β.surjective x`. Conclude with `SetLike.ext_iff.1 h y`.
-/
theorem eq_of_preimage_eq (β : X' ⟶ X) [Surjective β] {U V : X.Opens} (h : β ⁻¹ᵁ U = β ⁻¹ᵁ V) :
    U = V := by
  ext x
  obtain ⟨y, rfl⟩ := β.surjective x
  exact SetLike.ext_iff.1 h y

/- English proof (translation)
Use `GlobalTheory.LB.appLE_resG β h le_rfl x` as an intermediate fact. Rewrite `this` using `[Scheme.Hom.appLE_eq_app]`. Conclude with `this`.
-/
theorem app_rs (β : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (β.app V).hom (rs X h x) = rs X' (β.preimage_mono h) ((β.app U).hom x) := by
  have := GlobalTheory.LB.appLE_resG β h le_rfl x
  rw [Scheme.Hom.appLE_eq_app] at this
  exact this

/- English proof (translation)
Take `⟨t, rfl⟩ : ∃ t, (β.app V).hom t = s` from `β.app_surjective V hV s`. Take `rfl : X.basicOpen t = O` from `eq_of_preimage_eq β ((Scheme.preimage_basicOpen β t).trans hs)`. Establish `hε : (β.app _).hom (τ - rs X hO t) = 0`. Rewrite using `[map_sub, hτ, app_rs, sub_self]`. Take `⟨n, w, hw⟩ : ∃ (n : ℕ) (w : Γ(X, V)), rs X hO w = rs X hO t ^ n * (τ - rs X hO t)` from `exists_eq_pow_mul_of_isAffineOpen X V hV t (τ - rs X hO t)`.

Establish `h₁ : rs X' (β.preimage_mono hO) ((β.app V).hom w) = 0`. Rewrite using `[← app_rs β hO, hw, map_mul, hε, mul_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨l, hl⟩ : ∃ l : ℕ, (β.app V).hom t ^ l * (β.app V).hom w = 0 := by`. Use `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X' (hV.preimage β) _ _ ?_` and prove the remaining obligations. Use `congrArg (rs X' hs.le) h₁` as an intermediate fact.

Rewrite `this` using `[rs_rs, map_zero]`. Conclude with `this`. Use `⟨n + l + 1, fun k hk => ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩ : ∃ j, k = (n + l + j) + 1` from `⟨k - (n + l + 1), by omega⟩`. Use `⟨t ^ (n + l + j + 1) + ((n + l + j + 1 : ℕ) : Γ(X, V)) * (t ^ j * (t ^ l * w)), ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, map_pow, hl, mul_zero, add_zero]`. Establish `e` using `add_pow_succ_of_mul_self (rs X hO t) (τ - rs X hO t) (hsq _ _ _ hε hε) (n + l + j)`. Rewrite `e` using `[add_sub_cancel]`. Rewrite using `[e, map_add, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_natCast, hw]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_lift_pow (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β]
    (hsq : ∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0)
    {V O : X.Opens} (hV : IsAffineOpen V) (hO : O ≤ V) (τ : Γ(X, O)) (s : Γ(X', β ⁻¹ᵁ V))
    (hs : X'.basicOpen s = β ⁻¹ᵁ O) (hτ : (β.app O).hom τ = rs X' (β.preimage_mono hO) s) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∃ σ : Γ(X, V), (β.app V).hom σ = s ^ k ∧ rs X hO σ = τ ^ k := by
  obtain ⟨t, rfl⟩ : ∃ t, (β.app V).hom t = s := β.app_surjective V hV s
  obtain rfl : X.basicOpen t = O :=
    eq_of_preimage_eq β ((Scheme.preimage_basicOpen β t).trans hs)
  have hε : (β.app _).hom (τ - rs X hO t) = 0 := by
    rw [map_sub, hτ, app_rs, sub_self]
  obtain ⟨n, w, hw⟩ : ∃ (n : ℕ) (w : Γ(X, V)), rs X hO w = rs X hO t ^ n * (τ - rs X hO t) :=
    exists_eq_pow_mul_of_isAffineOpen X V hV t (τ - rs X hO t)
  have h₁ : rs X' (β.preimage_mono hO) ((β.app V).hom w) = 0 := by
    rw [← app_rs β hO, hw, map_mul, hε, mul_zero]
  obtain ⟨l, hl⟩ : ∃ l : ℕ, (β.app V).hom t ^ l * (β.app V).hom w = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X' (hV.preimage β) _ _ ?_
    have := congrArg (rs X' hs.le) h₁
    rw [rs_rs, map_zero] at this
    exact this
  refine ⟨n + l + 1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = (n + l + j) + 1 := ⟨k - (n + l + 1), by omega⟩
  refine ⟨t ^ (n + l + j + 1) + ((n + l + j + 1 : ℕ) : Γ(X, V)) * (t ^ j * (t ^ l * w)), ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow, hl, mul_zero, add_zero]
  · have e := add_pow_succ_of_mul_self (rs X hO t) (τ - rs X hO t) (hsq _ _ _ hε hε) (n + l + j)
    rw [add_sub_cancel] at e
    rw [e, map_add, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_natCast, hw]
    ring

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℕ, x ^ m * (y - x) = 0 := by`. Use `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hW _ _ ?_` and prove the remaining obligations. Use `congrArg (rs X hx) h` as an intermediate fact. Rewrite `this` using `[rs_rs, rs_rs]`. Express the relevant statement in the definitionally equal form `rs X (hx.trans hO) (y - x) = 0`.

Rewrite using `[map_sub, this, sub_self]`. Use `⟨m + 1, fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨j, rfl⟩ : ∃ j, l = (j + m) + 1` from `⟨l - (m + 1), by omega⟩`. Establish `e` using `add_pow_succ_of_mul_self x (y - x) hsq (j + m)`. Rewrite `e` using `[add_sub_cancel, pow_add x j m, _root_.mul_assoc, hm]`.

Simplify using `using e.symm`.
-/
theorem exists_pow_eq {W O : X.Opens} (hW : IsCompact (W : Set X)) (hO : O ≤ W) (x y : Γ(X, W))
    (hsq : (y - x) * (y - x) = 0) (hx : X.basicOpen x ≤ O) (h : rs X hO x = rs X hO y) :
    ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → x ^ l = y ^ l := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, x ^ m * (y - x) = 0 := by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hW _ _ ?_
    have := congrArg (rs X hx) h
    rw [rs_rs, rs_rs] at this
    change rs X (hx.trans hO) (y - x) = 0
    rw [map_sub, this, sub_self]
  refine ⟨m + 1, fun l hl => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, l = (j + m) + 1 := ⟨l - (m + 1), by omega⟩
  have e := add_pow_succ_of_mul_self x (y - x) hsq (j + m)
  rw [add_sub_cancel, pow_add x j m, _root_.mul_assoc, hm] at e
  simpa using e.symm

/- English proof (translation)
Establish `h : ∀ x : X, ∃ (V : X.Opens) (i : H.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ H.U i` using `fun x => by`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))`. Take `⟨_, ⟨V, hV, rfl⟩, hx, hle⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hi (H.U i).isOpen`. Conclude with `⟨V, i, hV, hx, hle⟩`. Use `choose V c hV hx hle using h`.

Take `⟨S, hS⟩` from `isCompact_univ.elim_finite_subcover (fun x => (V x : Set X)) (fun x => (V x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩`. Use `⟨S, inferInstance, fun a => V a, fun a => c a, fun a => hV a, fun a => hle a, fun x _ => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, hxa⟩` from `Set.mem_iUnion₂.1 (hS (Set.mem_univ x))`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩`.
-/
theorem exists_finite_affine_cover [CompactSpace X] {H : LB X} (hH : H.IsLB) :
    ∃ (I : Type) (_ : Finite I) (V : I → X.Opens) (c : I → H.ι),
      (∀ a, IsAffineOpen (V a)) ∧ (∀ a, V a ≤ H.U (c a)) ∧ ⊤ ≤ ⨆ a, V a := by
  have h : ∀ x : X, ∃ (V : X.Opens) (i : H.ι), IsAffineOpen V ∧ x ∈ V ∧ V ≤ H.U i := fun x => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (Set.mem_univ x))
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hi (H.U i).isOpen
    exact ⟨V, i, hV, hx, hle⟩
  choose V c hV hx hle using h
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩
  refine ⟨S, inferInstance, fun a => V a, fun a => c a, fun a => hV a, fun a => hle a, fun x _ => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `le_inf (X.basicOpen_le _) ?_ erw [Scheme.basicOpen_res]` and prove the remaining obligations. Conclude with `inf_le_right.trans (le_iSup (fun k => X.basicOpen (s.f k)) i)`. Establish `hu` using `SecOn.isUnit_rs_of_le_nonzeroLocus s i (O := V ⊓ nonzeroLocus s) (inf_le_left.trans h) inf_le_right`. Rewrite `hu` using `[← rs_rs h inf_le_left]`.

Establish `e` using `X.basicOpen_of_isUnit hu`. Use `erw [Scheme.basicOpen_res] at e`. Conclude with `e.ge.trans inf_le_right`.
-/
theorem basicOpen_rs_eq {H : LB X} (s : LB.Sec H) (i : H.ι) {V : X.Opens} (h : V ≤ H.U i) :
    X.basicOpen (rs X h (s.f i)) = V ⊓ nonzeroLocus s := by
  apply le_antisymm
  · refine le_inf (X.basicOpen_le _) ?_
    erw [Scheme.basicOpen_res]
    exact inf_le_right.trans (le_iSup (fun k => X.basicOpen (s.f k)) i)
  · have hu := SecOn.isUnit_rs_of_le_nonzeroLocus s i (O := V ⊓ nonzeroLocus s)
      (inf_le_left.trans h) inf_le_right
    rw [← rs_rs h inf_le_left] at hu
    have e := X.basicOpen_of_isUnit hu
    erw [Scheme.basicOpen_res] at e
    exact e.ge.trans inf_le_right

/- English proof (translation)
Introduce `X X' β _ _ _ _ hsq H hH s₀ D hD t ht`. Take `⟨I, _, V, c, hV, hc, hcov⟩` from `exists_finite_affine_cover hH`. Set `s (a : I) : Γ(X', β ⁻¹ᵁ V a)` to `rs X' (le_pull H β (hc a)) (s₀.f fun _ => c a)`. Set `τ (a : I) : Γ(X, V a ⊓ D)` to `rs X (le_inf inf_le_right (inf_le_left.trans (hc a))) (GlobalTheory.LB.coord t (c a))`. Establish `hs (a : I) : X'.basicOpen (s a) = β ⁻¹ᵁ (V a ⊓ D)` using `(basicOpen_rs_eq s₀ (fun _ => c a) (le_pull H β (hc a))).trans (congrArg (β ⁻¹ᵁ V a ⊓ ·) hD.symm)`.

Establish `hτ (a : I) : (β.app _).hom (τ a) = rs X' (β.preimage_mono inf_le_left) (s a)`. Establish `e` using `congrArg (fun z => rs X' (le_inf (β.preimage_mono inf_le_right) (le_pull H β (inf_le_left.trans (hc a))) : β ⁻¹ᵁ (V a ⊓ D) ≤ β ⁻¹ᵁ D ⊓ (H.pull β).U fun _ => c a) (GlobalTheory.LB.coord z fun _ => c a)) ht`. Rewrite using `[app_rs, rs_rs]`. Conclude with `((GlobalTheory.LB.resG_appLE β _ _ _).symm.trans e).trans (rs_rs _ _ _)`. Use `choose k₀ hk₀ using fun a => exists_lift_pow β hsq (hV a) inf_le_left (τ a) (s a) (hs a) (hτ a)`.

Take `⟨k₁, hk₁⟩` from `(Set.finite_range k₀).bddAbove`. Use `choose σ hσs hστ using fun a => hk₀ a (k₁ + 1) ((hk₁ ⟨a, rfl⟩).trans (Nat.le_succ _))`. Establish `hbo (a : I) : X.basicOpen (σ a) = V a ⊓ D`. Use `eq_of_preimage_eq β ((Scheme.preimage_basicOpen β _).trans ?_)` and prove the remaining obligations. Rewrite using `[← hs, ← X'.basicOpen_pow (s a) (Nat.succ_pos k₁)]`.

Conclude with `congrArg X'.basicOpen (hσs a)`. Set `g (a b : I) : Γ(X, V a ⊓ V b)` to `rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b)).val`. Establish `key (p : I × I) : ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → rs X inf_le_left (σ p.1) ^ l = (g p.1 p.2 ^ (k₁ + 1) * rs X inf_le_right (σ p.2)) ^ l`. Take `⟨a, b⟩` from `p`. Establish `hsm : (β.app _).hom (g a b ^ (k₁ + 1) * rs X inf_le_right (σ b) - rs X inf_le_left (σ a)) = 0`.

Establish `e` using `GlobalTheory.LB.sec_rel s₀ (fun _ => c a) (fun _ => c b) (W := β ⁻¹ᵁ (V a ⊓ V b)) (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b))) (le_inf (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b))))`. Use `erw [GlobalTheory.LB.resG_pull_g] at e`. Rewrite using `[map_sub, map_mul, map_pow, app_rs, app_rs, app_rs, hσs, hσs, map_pow, map_pow, rs_rs, rs_rs, ← mul_pow, sub_eq_zero]`. Conclude with `congrArg (· ^ (k₁ + 1)) e.symm`. Use `exists_pow_eq (O := V a ⊓ V b ⊓ D) (QuasiSeparatedSpace.inter_isCompact _ _ (V a).isOpen (hV a).isCompact (V b).isOpen (hV b).isCompact) inf_le_left _ _ (hsq _ _ _ hsm hsm) ?_ ?_` and prove the remaining obligations.

Use `erw [Scheme.basicOpen_res]`. Rewrite using `[hbo]`. Conclude with `inf_le_inf_left _ inf_le_right`. Establish `ea` using `congrArg (rs X (inf_le_inf_right D inf_le_left : V a ⊓ V b ⊓ D ≤ V a ⊓ D)) (hστ a)`. Establish `eb` using `congrArg (rs X (inf_le_inf_right D inf_le_right : V a ⊓ V b ⊓ D ≤ V b ⊓ D)) (hστ b)`.

Rewrite `ea`, `eb` using `[rs_rs, map_pow, rs_rs]`. Rewrite using `[map_mul, map_pow, rs_rs, rs_rs, rs_rs, ea, eb, ← mul_pow]`. Conclude with `congrArg (· ^ (k₁ + 1)) (SecOn.compat t (c a) (c b) _ _ _)`. Use `choose l₀ hl₀ using key`. Take `⟨l₁, hl₁⟩` from `(Set.finite_range l₀).bddAbove`.

Take `⟨u, hu, -⟩` from `SecOn.existsUnique_of_local (V := ⊤) (isLB_pw hH (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)) V (fun _ => le_top) hcov c hc (fun a => σ a ^ (l₁ + 1)) fun a b => by`. Establish `e` using `hl₀ (a, b) (l₁ + 1) ((hl₁ ⟨(a, b), rfl⟩).trans (Nat.le_succ _))`. Rewrite `e` using `[mul_pow, ← pow_mul]`. Rewrite using `[map_pow, map_pow]`. Use `e.trans (congrArg (· * _) ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b) ^ (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)).val`. Rewrite using `[zpow_natCast, Units.val_pow_eq_pow_val, map_pow]`. Use `⟨(k₁ + 1) * (l₁ + 1), Nat.succ_le_of_lt (by positivity), SecOn.topEquiv _ u, ?_⟩` and prove the remaining obligations. Establish `hloc (a : I) : V a ⊓ nonzeroLocus (SecOn.topEquiv _ u) = V a ⊓ D`. Rewrite using `[← basicOpen_rs_eq (SecOn.topEquiv _ u) (c a) (hc a), ← hbo, ← X.basicOpen_pow (σ a) (Nat.succ_pos l₁)]`.

Conclude with `congrArg X.basicOpen ((rs_rs _ _ _).trans (hu a))`. Use extensionality with `x`. Take `⟨a, ha⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hcov (Set.mem_univ x))`. Establish `e` using `SetLike.ext_iff.1 (hloc a) x`. Conclude with `⟨fun h => (e.1 ⟨ha, h⟩).2, fun h => (e.2 ⟨ha, h⟩).2⟩`.
-/
theorem exists_pow_section : ∀ (X X' : Scheme.{0}) (β : X' ⟶ X) [IsClosedImmersion β] [Surjective β] [CompactSpace X] [QuasiSeparatedSpace X], (∀ (W : X.Opens) (x y : Γ(X, W)), (β.app W).hom x = 0 → (β.app W).hom y = 0 → x * y = 0) → ∀ H : LB X, H.IsLB → ∀ (s₀ : LB.Sec (H.pull β)) (D : X.Opens), β ⁻¹ᵁ D = nonzeroLocus s₀ → ∀ t : SecOn H D, SecOn.pull H β D t = GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D) → ∃ n : ℕ, 1 ≤ n ∧ ∃ σ : LB.Sec (pw H n), nonzeroLocus σ = D := by
  intro X X' β _ _ _ _ hsq H hH s₀ D hD t ht
  obtain ⟨I, _, V, c, hV, hc, hcov⟩ := exists_finite_affine_cover hH
  let s (a : I) : Γ(X', β ⁻¹ᵁ V a) := rs X' (le_pull H β (hc a)) (s₀.f fun _ => c a)
  let τ (a : I) : Γ(X, V a ⊓ D) :=
    rs X (le_inf inf_le_right (inf_le_left.trans (hc a))) (GlobalTheory.LB.coord t (c a))
  have hs (a : I) : X'.basicOpen (s a) = β ⁻¹ᵁ (V a ⊓ D) :=
    (basicOpen_rs_eq s₀ (fun _ => c a) (le_pull H β (hc a))).trans
      (congrArg (β ⁻¹ᵁ V a ⊓ ·) hD.symm)
  have hτ (a : I) : (β.app _).hom (τ a) = rs X' (β.preimage_mono inf_le_left) (s a) := by
    have e := congrArg (fun z => rs X' (le_inf (β.preimage_mono inf_le_right)
      (le_pull H β (inf_le_left.trans (hc a))) :
        β ⁻¹ᵁ (V a ⊓ D) ≤ β ⁻¹ᵁ D ⊓ (H.pull β).U fun _ => c a) (GlobalTheory.LB.coord z fun _ => c a)) ht
    rw [app_rs, rs_rs]
    exact ((GlobalTheory.LB.resG_appLE β _ _ _).symm.trans e).trans (rs_rs _ _ _)
  choose k₀ hk₀ using fun a => exists_lift_pow β hsq (hV a) inf_le_left (τ a) (s a) (hs a) (hτ a)
  obtain ⟨k₁, hk₁⟩ := (Set.finite_range k₀).bddAbove
  choose σ hσs hστ using fun a => hk₀ a (k₁ + 1) ((hk₁ ⟨a, rfl⟩).trans (Nat.le_succ _))
  have hbo (a : I) : X.basicOpen (σ a) = V a ⊓ D := by
    refine eq_of_preimage_eq β ((Scheme.preimage_basicOpen β _).trans ?_)
    rw [← hs, ← X'.basicOpen_pow (s a) (Nat.succ_pos k₁)]
    exact congrArg X'.basicOpen (hσs a)
  let g (a b : I) : Γ(X, V a ⊓ V b) := rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b)).val
  have key (p : I × I) : ∃ l₀ : ℕ, ∀ l, l₀ ≤ l → rs X inf_le_left (σ p.1) ^ l =
      (g p.1 p.2 ^ (k₁ + 1) * rs X inf_le_right (σ p.2)) ^ l := by
    obtain ⟨a, b⟩ := p
    have hsm : (β.app _).hom (g a b ^ (k₁ + 1) * rs X inf_le_right (σ b) -
        rs X inf_le_left (σ a)) = 0 := by
      have e := GlobalTheory.LB.sec_rel s₀ (fun _ => c a) (fun _ => c b) (W := β ⁻¹ᵁ (V a ⊓ V b))
        (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b)))
        (le_inf (le_pull H β (inf_le_left.trans (hc a))) (le_pull H β (inf_le_right.trans (hc b))))
      erw [GlobalTheory.LB.resG_pull_g] at e
      rw [map_sub, map_mul, map_pow, app_rs, app_rs, app_rs, hσs, hσs, map_pow, map_pow, rs_rs, rs_rs,
        ← mul_pow, sub_eq_zero]
      exact congrArg (· ^ (k₁ + 1)) e.symm
    refine exists_pow_eq (O := V a ⊓ V b ⊓ D)
      (QuasiSeparatedSpace.inter_isCompact _ _ (V a).isOpen (hV a).isCompact (V b).isOpen
        (hV b).isCompact) inf_le_left _ _ (hsq _ _ _ hsm hsm) ?_ ?_
    · erw [Scheme.basicOpen_res]
      rw [hbo]
      exact inf_le_inf_left _ inf_le_right
    · have ea := congrArg (rs X (inf_le_inf_right D inf_le_left : V a ⊓ V b ⊓ D ≤ V a ⊓ D)) (hστ a)
      have eb := congrArg (rs X (inf_le_inf_right D inf_le_right : V a ⊓ V b ⊓ D ≤ V b ⊓ D)) (hστ b)
      rw [rs_rs, map_pow, rs_rs] at ea eb
      rw [map_mul, map_pow, rs_rs, rs_rs, rs_rs, ea, eb, ← mul_pow]
      exact congrArg (· ^ (k₁ + 1)) (SecOn.compat t (c a) (c b) _ _ _)
  choose l₀ hl₀ using key
  obtain ⟨l₁, hl₁⟩ := (Set.finite_range l₀).bddAbove
  obtain ⟨u, hu, -⟩ := SecOn.existsUnique_of_local (V := ⊤)
    (isLB_pw hH (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)) V (fun _ => le_top) hcov c hc
    (fun a => σ a ^ (l₁ + 1)) fun a b => by
      have e := hl₀ (a, b) (l₁ + 1) ((hl₁ ⟨(a, b), rfl⟩).trans (Nat.le_succ _))
      rw [mul_pow, ← pow_mul] at e
      rw [map_pow, map_pow]
      refine e.trans (congrArg (· * _) ?_)
      change _ = rs X (inf_le_inf (hc a) (hc b)) (H.g (c a) (c b) ^ (((k₁ + 1) * (l₁ + 1) : ℕ) : ℤ)).val
      rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  refine ⟨(k₁ + 1) * (l₁ + 1), Nat.succ_le_of_lt (by positivity), SecOn.topEquiv _ u, ?_⟩
  have hloc (a : I) : V a ⊓ nonzeroLocus (SecOn.topEquiv _ u) = V a ⊓ D := by
    rw [← basicOpen_rs_eq (SecOn.topEquiv _ u) (c a) (hc a), ← hbo,
      ← X.basicOpen_pow (σ a) (Nat.succ_pos l₁)]
    exact congrArg X.basicOpen ((rs_rs _ _ _).trans (hu a))
  ext x
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov (Set.mem_univ x))
  have e := SetLike.ext_iff.1 (hloc a) x
  exact ⟨fun h => (e.1 ⟨ha, h⟩).2, fun h => (e.2 ⟨ha, h⟩).2⟩

end GlobalTheory.SecPow
