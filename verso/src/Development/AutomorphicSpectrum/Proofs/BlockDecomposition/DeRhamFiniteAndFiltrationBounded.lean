import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.KFin

section Gen

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj K n).1 x`. Take `⟨b, hb, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj K n).1 y`. Establish `e : a = b` using `h.elim _ _`. Substitute `e` using the available equality.

Both sides reduce to the same expression.
-/
theorem cx_H_subsingleton (K : Cx.{1} R) (n : ℕ) (h : Subsingleton (K.X n)) : Subsingleton (K.H n) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 x
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj K n).1 y
  have e : a = b := h.elim _ _
  subst e
  rfl

/- English proof (translation)
The claim follows from `cx_H_subsingleton (CH.cx F) n ⟨fun a b => funext fun s => (h _).elim _ _⟩`.
-/
theorem H_subsingleton (F : C ⥤ ModuleCat.{0} R) (h : ∀ T, Subsingleton (F.obj T)) (n : ℕ) :
    Subsingleton (CH.H F n) :=
  cx_H_subsingleton (CH.cx F) n ⟨fun a b => funext fun s => (h _).elim _ _⟩

/- English proof (translation)
Take `⟨x, hx⟩` from `x`. Take `⟨y, hy, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx`. Conclude with `⟨y, hy, rfl⟩`.
-/
theorem sqM_rep (a b : IdF A) (T : C) (x : sqM a b T) :
    ∃ (y : A.obj T) (hy : y ∈ a.S T), x = sqMk a b y hy := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨y, hy, rfl⟩

/- English proof (translation)
Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Take `⟨x', hx, rfl⟩` from `sqM_rep a a T x`. Take `⟨y', hy, rfl⟩` from `sqM_rep a a T y`. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ x' = Ideal.Quotient.mk _ y'`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hx, Ideal.Quotient.eq_zero_iff_mem.2 hy]`.
-/
theorem sq_self_subsingleton (a : IdF A) (T : C) : Subsingleton ((sq a a).obj T) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', hx, rfl⟩ := sqM_rep a a T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep a a T y
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ x' = Ideal.Quotient.mk _ y'
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, Ideal.Quotient.eq_zero_iff_mem.2 hy]

variable {a b c : IdF A}

/- English proof (translation)
Introduce `x y h`. Take `⟨x', hx, rfl⟩` from `sqM_rep b c T x`. Take `⟨y', hy, rfl⟩` from `sqM_rep b c T y`. Establish `h'` using `congrArg (fun z : sqM a c T => z.1) h`. Conclude with `Subtype.ext h'`.
-/
theorem sq_inj (hba : ∀ T, b.S T ≤ a.S T) (T : C) :
    Function.Injective ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T) := by
  intro x y h
  obtain ⟨x', hx, rfl⟩ := sqM_rep b c T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep b c T y
  have h' := congrArg (fun z : sqM a c T => z.1) h
  exact Subtype.ext h'

/- English proof (translation)
Introduce `x`. Take `⟨x', hx, rfl⟩` from `sqM_rep a c T x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : (Ideal.Quotient.mk (b.S T) x') = 0` using `congrArg Subtype.val h`.

Conclude with `⟨sqMk b c x' (Ideal.Quotient.eq_zero_iff_mem.1 h'), rfl⟩`. Introduce and unpack `⟨y, hy⟩`. Take `⟨y', hy', rfl⟩` from `sqM_rep b c T y`. Establish `e : (Ideal.Quotient.mk (c.S T) y') = Ideal.Quotient.mk (c.S T) x'` using `congrArg Subtype.val hy`. Use `Subtype.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (b.S T) x' = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Use `Ideal.Quotient.eq.1 e` as an intermediate fact. Establish `h2` using `hcb T this`. Establish `h3` using `(b.S T).sub_mem hy' h2`.

Simplify using `using h3`.
-/
theorem sq_exact (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a c T x
  constructor
  · intro h
    have h' : (Ideal.Quotient.mk (b.S T) x') = 0 := congrArg Subtype.val h
    exact ⟨sqMk b c x' (Ideal.Quotient.eq_zero_iff_mem.1 h'), rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y', hy', rfl⟩ := sqM_rep b c T y
    have e : (Ideal.Quotient.mk (c.S T) y') = Ideal.Quotient.mk (c.S T) x' := congrArg Subtype.val hy
    refine Subtype.ext ?_
    change Ideal.Quotient.mk (b.S T) x' = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := Ideal.Quotient.eq.1 e
    have h2 := hcb T this
    have h3 := (b.S T).sub_mem hy' h2
    simpa using h3

/- English proof (translation)
Introduce `x`. Take `⟨x', hx, rfl⟩` from `sqM_rep a b T x`. Conclude with `⟨sqMk a c x' hx, rfl⟩`.
-/
theorem sq_surj (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Surjective ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a b T x
  exact ⟨sqMk a c x' hx, rfl⟩

/- English proof (translation)
Take `⟨δ, -, -, e, -⟩` from `CrystallineSemistableComparison.P.les (sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).hom (sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).hom (fun n x y h => funext fun s => sq_inj hba _ (congrFun h s)) (fun n y => ⟨fun hy => ⟨fun s => ((sq_exa …`. Use function extensionality and compare the values at `fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose_spec⟩, by`. Introduce and unpack `⟨x, rfl⟩`. Use function extensionality and compare the values at `s`. Conclude with `(sq_exact hba hcb _ _).2 ⟨_, rfl⟩⟩)`.

Use the proof step `(fun n y => ⟨fun s => (sq_surj hcb _ (y s)).choose, funext fun s => (sq_surj hcb _ (y s)).choose_spec⟩)`. Conclude with `e n`.
-/
theorem sq_les (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (n : ℕ) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).pull n)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).pull n) := by
  obtain ⟨δ, -, -, e, -⟩ := CrystallineSemistableComparison.P.les
    (sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).hom
    (sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).hom
    (fun n x y h => funext fun s => sq_inj hba _ (congrFun h s))
    (fun n y => ⟨fun hy => ⟨fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose,
        funext fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose_spec⟩, by
      rintro ⟨x, rfl⟩
      funext s
      exact (sq_exact hba hcb _ _).2 ⟨_, rfl⟩⟩)
    (fun n y => ⟨fun s => (sq_surj hcb _ (y s)).choose, funext fun s => (sq_surj hcb _ (y s)).choose_spec⟩)
  exact e n

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `r _ h`. Take `rfl : r = s` from `by omega`.

Conclude with `𝒮.zero _ (H_subsingleton _ (sq_self_subsingleton _) n)`. Consider the case `succ d ih`. Introduce `r h0 h`. Conclude with `𝒮.mid _ _ _ _ _ (sq_les (hanti r (r + 1) (by omega)) (hanti (r + 1) s (by omega)) n) (ih (r + 1) (by omega) (by omega)) (hgr r h0 (by omega))`.
-/
theorem dev (𝒮 : Serre.{1} R) (a : ℕ → IdF A) (hanti : ∀ k l, k ≤ l → ∀ T, (a l).S T ≤ (a k).S T)
    (s n r₀ : ℕ) (hgr : ∀ r, r₀ ≤ r → r < s → 𝒮.P (CH.H (sq (a r) (a (r + 1))) n)) :
    ∀ (d r : ℕ), r₀ ≤ r → r + d = s → 𝒮.P (CH.H (sq (a r) (a s)) n) := by
  intro d
  induction d with
  | zero =>
    intro r _ h
    obtain rfl : r = s := by omega
    exact 𝒮.zero _ (H_subsingleton _ (sq_self_subsingleton _) n)
  | succ d ih =>
    intro r h0 h
    exact 𝒮.mid _ _ _ _ _ (sq_les (hanti r (r + 1) (by omega)) (hanti (r + 1) s (by omega)) n)
      (ih (r + 1) (by omega) (by omega)) (hgr r h0 (by omega))

def zeroSerre (R : Type) [CommRing R] : Serre.{1} R where
  P M _ _ := Subsingleton M
  zero _ _ _ h := h
  mid M₁ M₂ M₃ _ _ _ _ _ _ f g e h₁ h₃ := ⟨fun x y => by
    have key : ∀ z : M₂, z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := (e z).1 (h₃.elim _ _)
      rw [h₁.elim w 0, map_zero]
    rw [key x, key y]⟩

/- English proof (translation)
Use `CrystallineSemistableComparison.P.mapH_bij (toSq a b ha).hom (fun n => ⟨fun x y h => funext fun s => ?_, fun y => ?_⟩) n` and prove the remaining obligations. Establish `h'` using `congrArg (fun z : sqM a b _ => z.1) (congrFun h s)`. Use `Ideal.Quotient.eq.1 h'` as an intermediate fact. Rewrite `this` using `[hb]`. Establish `h2 : (show A.obj (s.obj (Fin.last _)) from x s) - (show A.obj (s.obj (Fin.last _)) from y s) = 0` using `(Ideal.mem_bot).1 this`.

Conclude with `sub_eq_zero.1 h2`. Establish `key : ∀ (T : C) (z : (sq a b).obj T), ∃ w : (CH.modF A).obj T, (toSq a b ha).τ T w = z`. Introduce `T z`. Take `⟨w, hw, rfl⟩` from `sqM_rep a b T z`. Conclude with `⟨w, rfl⟩`.

Conclude with `⟨fun s => (key _ (y s)).choose, funext fun s => (key _ (y s)).choose_spec⟩`.
-/
theorem toSq_bijective (a b : IdF A) (ha : ∀ T, a.S T = ⊤) (hb : ∀ T, b.S T = ⊥) (n : ℕ) :
    Function.Bijective ((toSq a b ha).pull n) := by
  refine CrystallineSemistableComparison.P.mapH_bij (toSq a b ha).hom (fun n => ⟨fun x y h => funext fun s => ?_, fun y => ?_⟩) n
  · have h' := congrArg (fun z : sqM a b _ => z.1) (congrFun h s)
    have := Ideal.Quotient.eq.1 h'
    rw [hb] at this
    have h2 : (show A.obj (s.obj (Fin.last _)) from x s) - (show A.obj (s.obj (Fin.last _)) from y s) = 0 := (Ideal.mem_bot).1 this
    exact sub_eq_zero.1 h2
  · have key : ∀ (T : C) (z : (sq a b).obj T), ∃ w : (CH.modF A).obj T, (toSq a b ha).τ T w = z := by
      intro T z
      obtain ⟨w, hw, rfl⟩ := sqM_rep a b T z
      exact ⟨w, rfl⟩
    exact ⟨fun s => (key _ (y s)).choose, funext fun s => (key _ (y s)).choose_spec⟩

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `(CrystallineSemistableComparison.P.cls_surj _ n).1 y`. Both sides reduce to the same expression.
-/
theorem toSq_comp (a b c : IdF A) (ha : ∀ T, a.S T = ⊤) (hcb : ∀ T, c.S T ≤ b.S T) (n : ℕ)
    (y : CH.H (CH.modF A) n) :
    (sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).pull n ((toSq a c ha).pull n y) =
      (toSq a b ha).pull n y := by
  obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 y
  rfl

end Gen

/- English proof (translation)
Use `Ideal.span_eq_bot.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨l, hl, hr, rfl⟩`. Establish `: ∃ q ∈ l, q.1 ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `: (l.map Prod.fst).sum = 0`. Use `List.sum_eq_zero ?_` and prove the remaining obligations. Introduce `x hx`. Take `⟨q, hq, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hc q hq`.

Use linear arithmetic over natural numbers and integers. Take `⟨q, hq, h0⟩` from `this`. Use `List.prod_eq_zero (List.mem_map.2 ⟨q, hq, ?_⟩)` and prove the remaining obligations. Establish `e : q.2 = 0` using `(Ideal.mem_bot).1 (hl q hq)`. Rewrite using `[e]`.

Conclude with `DividedPowers.dpow_eval_zero _ h0`. Use `tf r x h := by simpa using h`. Use `dv n hn := ⟨0, (n : K)⁻¹, by simp [Nat.cast_ne_zero.2 hn]⟩`.
-/
theorem tfBase (K : Type) [Field K] [CharZero K] (s : ℕ) (hs : 0 < s) : TFBase (dividedPowersBot K) 1 s where
  nil := by
    refine Ideal.span_eq_bot.2 ?_
    rintro _ ⟨l, hl, hr, rfl⟩
    have : ∃ q ∈ l, q.1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      have : (l.map Prod.fst).sum = 0 := by
        refine List.sum_eq_zero ?_
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact hc q hq
      omega
    obtain ⟨q, hq, h0⟩ := this
    refine List.prod_eq_zero (List.mem_map.2 ⟨q, hq, ?_⟩)
    have e : q.2 = 0 := (Ideal.mem_bot).1 (hl q hq)
    rw [e]
    exact DividedPowers.dpow_eval_zero _ h0
  tf r x h := by simpa using h
  dv n hn := ⟨0, (n : K)⁻¹, by simp [Nat.cast_ne_zero.2 hn]⟩

end GlobalTheory.CompanionTheory.KFin

namespace GlobalTheory.CompanionTheory.KFin

section Spec

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, W, hW, hi⟩`. Take `rfl : W = V` from `hW`. Conclude with `⟨h, hi⟩`. Introduce and unpack `⟨h, hi⟩`.

Conclude with `⟨h, V, rfl, hi⟩`.
-/
theorem st_single_iff {Q : ObjectProperty (Thick (smFun X q))} {V : X.Opens} (T : Thick (smFun X q)) :
    St Q {V} T ↔ Q T ∧ InU V T := by
  constructor
  · rintro ⟨h, W, hW, hi⟩
    obtain rfl : W = V := hW
    exact ⟨h, hi⟩
  · rintro ⟨h, hi⟩
    exact ⟨h, V, rfl, hi⟩

/- English proof (translation)
Use function extensionality and compare the values at `T`. Use `propext ⟨fun h => ?_, fun h a => ?_⟩` and prove the remaining obligations. Use `(st_single_iff T).2 ⟨((st_single_iff T).1 (h 0)).1, (GlobalTheory.T.inOpen_finite_inf_iff U _ T).2 fun α hα => ?_⟩` and prove the remaining obligations. Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 hα`. Conclude with `((st_single_iff T).1 (h a)).2`.

Take `⟨h1, h2⟩` from `(st_single_iff T).1 h`. Conclude with `(st_single_iff T).2 ⟨h1, (GlobalTheory.T.inOpen_finite_inf_iff U _ T).1 h2 _ (Finset.mem_image_of_mem i (Finset.mem_univ a))⟩`.
-/
theorem capT_eq (Q : ObjectProperty (Thick (smFun X q))) {ι : Type} [DecidableEq ι] (U : ι → X.Opens) {n : ℕ}
    (i : Fin (n + 1) → ι) :
    capT (fun α => St Q {U α}) i = St Q {⨅ α ∈ Finset.univ.image i, U α} := by
  funext T
  refine propext ⟨fun h => ?_, fun h a => ?_⟩
  · refine (st_single_iff T).2 ⟨((st_single_iff T).1 (h 0)).1, (GlobalTheory.T.inOpen_finite_inf_iff U _ T).2 fun α hα => ?_⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
    exact ((st_single_iff T).1 (h a)).2
  · obtain ⟨h1, h2⟩ := (st_single_iff T).1 h
    exact (st_single_iff T).2 ⟨h1, (GlobalTheory.T.inOpen_finite_inf_iff U _ T).1 h2 _ (Finset.mem_image_of_mem i (Finset.mem_univ a))⟩

/- English proof (translation)
The claim follows from `(hVan (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U.U r).1 (fun S hS j' hj' => hAff q _ (U.inter S hS) s r j' hr (by omega)) j hj`.
-/
theorem gr_van (hVan : KH.GlobVanSt) (hAff : KH.GrAff) [Smooth q] (U : Cov q) (s r : ℕ) (hr : r < s) (j : ℕ) (hj : j < r) :
    Subsingleton (HQ (KS q s (Set.range U.U)) r ((r : ℤ) + 1) j) :=
  (hVan (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U.U r).1
    (fun S hS j' hj' => hAff q _ (U.inter S hS) s r j' hr (by omega)) j hj

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Use `hSerre (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U.U 𝒮 n fun a b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b = r`. Substitute `hb` using the available equality. Conclude with `(h𝒮 _).2 (hCech 1 s (tfBase K s hs) q U b hr a)`. Use `𝒮.zero _ (cx_H_subsingleton _ a ⟨fun x y => funext fun i => ?_⟩)` and prove the remaining obligations.

Establish `h` using `hAff q _ (U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ _)⟩) s r b hr hb`. Establish `e` using `capT_eq (K := K) (X := X) (q := q) (TF 1 s) U.U i`. Establish `h' : Subsingleton (HU (Pb.sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1))) (capT (fun α => St (TF 1 s) {U.U α}) i) b)`. Rewrite using `[e]`. Conclude with `h`.

Conclude with `h'.elim _ _`.
-/
theorem gr_fin (hSerre : KH.GlobSerreSt) (hAff : KH.GrAff) (hCech : KH.GrCechFin) [IsProper q] [Smooth q] (U : Cov q)
    (s : ℕ) (hs : 0 < s) (𝒮 : Serre.{1} K) (h𝒮 : ∀ (M : Type 1) [AddCommGroup M] [Module K M], 𝒮.P M ↔ Module.Finite K M)
    (r : ℕ) (hr : r < s) (n : ℕ) : 𝒮.P (HQ (KS q s (Set.range U.U)) r ((r : ℤ) + 1) n) := by
  classical
  refine hSerre (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U.U 𝒮 n fun a b _ => ?_
  by_cases hb : b = r
  · subst hb
    exact (h𝒮 _).2 (hCech 1 s (tfBase K s hs) q U b hr a)
  · refine 𝒮.zero _ (cx_H_subsingleton _ a ⟨fun x y => funext fun i => ?_⟩)
    have h := hAff q _ (U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem i (Finset.mem_univ _)⟩) s r b hr hb
    have e := capT_eq (K := K) (X := X) (q := q) (TF 1 s) U.U i
    have h' : Subsingleton (HU (Pb.sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
        (capT (fun α => St (TF 1 s) {U.U α}) i) b) := by
      rw [e]
      exact h
    exact h'.elim _ _

end Spec

end GlobalTheory.CompanionTheory.KFin

namespace GlobalTheory.CompanionTheory.KFin

/- English proof (translation)
The claim follows from `(GlobalTheory.T.sheaf_filtration_property Q).anti (by exact_mod_cast h) T`.
-/
theorem fil_anti {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (Q : ObjectProperty (Thick (smFun X q))) (k l : ℕ) (h : k ≤ l) (T) :
    (sFil Q (l : ℤ)).S T ≤ (sFil Q (k : ℤ)).S T :=
  (GlobalTheory.T.sheaf_filtration_property Q).anti (by exact_mod_cast h) T

/- English proof (translation)
The claim follows from `T.property.1.1`.
-/
theorem fil_bot {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ) (𝒱 : Set X.Opens) (T) :
    (sFil (KS q s 𝒱) (s : ℤ)).S T = ⊥ := T.property.1.1

end GlobalTheory.CompanionTheory.KFin

/- English proof (translation)
Introduce `_ _ _ hSerre hVan hK hAff hCech K _ _ X q _ _ j`. Take `⟨U⟩` from `(GlobalTheory.T.exists_smooth_coordinate_cover q).1 inferInstance`. Take `⟨𝒮, h𝒮⟩` from `GlobalTheory.T.finite_modules_serre_class K`. Set `s : ℕ` to `(Finset.univ.sup U.d) + j + 1`. Establish `hs : ∀ α, U.d α < s` using `fun α => by`.

Establish `: U.d α ≤ Finset.univ.sup U.d` using `Finset.le_sup (Finset.mem_univ α)`. Simplify using `only [s]`. Use linear arithmetic over natural numbers and integers. Establish `hs0 : 0 < s` using `by simp only [s]; omega`. Establish `hjs : j + 1 ≤ s` using `by simp only [s]; omega`.

Establish `hcov : sSup (Set.range U.U) = ⊤` using `by rw [sSup_range]; exact U.cover`. Take `⟨hbij, hfil⟩` from `hK q U s hs (Set.range U.U) hcov j`. Set `Q` to `KS q s (Set.range U.U)`. Set `a : ℕ → IdF (sP Q).A` to `fun r => sFil Q (r : ℤ)`. Establish `hanti : ∀ k l, k ≤ l → ∀ T, (a l).S T ≤ (a k).S T` using `fun k l h T => fil_anti q Q k l h T`.

Establish `htop : ∀ T : Q.FullSubcategory, (sFil Q 0).S T = ⊤` using `fun T => T.obj.pdPow_zero`. Establish `hqb : Function.Bijective (quoK q Q (s : ℤ) j)` using `(toSq_bijective (sFil Q 0) (sFil Q (s : ℤ)) htop (fil_bot q s _) j).comp hbij`. Establish `hgr : ∀ r, 0 ≤ r → r < s → 𝒮.P (CH.H (Pb.sq (a r) (a (r + 1))) j)` using `fun r _ hr => gr_fin hSerre hAff hCech U s hs0 𝒮 h𝒮 r hr j`. Establish `hP : 𝒮.P (CH.H (Pb.sq (a 0) (a s)) j)` using `dev 𝒮 a hanti s j 0 hgr s 0 le_rfl (by omega)`. Establish `hfinH : Module.Finite K (HQ Q 0 (s : ℤ) j)` using `(h𝒮 _).1 hP`.

Use `⟨Module.Finite.equiv (LinearEquiv.ofBijective (quoK q Q (s : ℤ) j) hqb).symm, ?_⟩` and prove the remaining obligations. Establish `hgv : ∀ r, j + 1 ≤ r → r < s → (zeroSerre K).P (CH.H (Pb.sq (a r) (a (r + 1))) j)` using `fun r h0 hr => gr_van hVan hAff U s r hr j h0`. Establish `hz : Subsingleton (CH.H (Pb.sq (a (j + 1)) (a s)) j)` using `dev (zeroSerre K) a hanti s j (j + 1) hgv (s - (j + 1)) (j + 1) le_rfl (by omega)`. Introduce `x hx`. Establish `h0 : quoK q Q ((j + 1 : ℕ) : ℤ) j x = 0` using `(hfil (j + 1) hjs x).1 hx`.

Establish `hcb : ∀ T, (sFil Q (s : ℤ)).S T ≤ (sFil Q ((j + 1 : ℕ) : ℤ)).S T` using `fun T => fil_anti q Q (j + 1) s hjs T`. Establish `hba : ∀ T, (sFil Q ((j + 1 : ℕ) : ℤ)).S T ≤ (sFil Q 0).S T` using `fun T => fil_anti q Q 0 (j + 1) (Nat.zero_le _) T`. Establish `h1 : (sqLe (a` using `sFil Q 0) (b := sFil Q (s : ℤ)) (a' := sFil Q 0) (b' := sFil Q ((j + 1 : ℕ) : ℤ)) (fun _ => le_rfl) hcb).pull j (quoK q Q (s : ℤ) j x) = 0 := by`. Rewrite using `[← h0]`. Conclude with `toSq_comp (sFil Q 0) (sFil Q ((j + 1 : ℕ) : ℤ)) (sFil Q (s : ℤ)) htop hcb j (resK q Q j x)`.

Take `⟨w, hw⟩` from `(sq_les (a := sFil Q 0) (b := sFil Q ((j + 1 : ℕ) : ℤ)) (c := sFil Q (s : ℤ)) hba hcb j _).1 h1`. Establish `hw0 : w = 0` using `hz.elim _ _`. Rewrite `hw` using `[hw0, map_zero]`. Conclude with `hqb.1 (by rw [← hw, map_zero])`.
-/
theorem GlobalTheory.CompanionTheory.KFin.main : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → KH.GrCechFin → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] (j : ℕ),
    FiniteDimensional K (HdR q j) ∧ ∀ x ∈ FilR q j (j + 1), x = 0 := by
  intro _ _ _ hSerre hVan hK hAff hCech K _ _ X q _ _ j
  obtain ⟨U⟩ := (GlobalTheory.T.exists_smooth_coordinate_cover q).1 inferInstance
  obtain ⟨𝒮, h𝒮⟩ := GlobalTheory.T.finite_modules_serre_class K
  let s : ℕ := (Finset.univ.sup U.d) + j + 1
  have hs : ∀ α, U.d α < s := fun α => by
    have : U.d α ≤ Finset.univ.sup U.d := Finset.le_sup (Finset.mem_univ α)
    simp only [s]; omega
  have hs0 : 0 < s := by simp only [s]; omega
  have hjs : j + 1 ≤ s := by simp only [s]; omega
  have hcov : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  obtain ⟨hbij, hfil⟩ := hK q U s hs (Set.range U.U) hcov j
  let Q := KS q s (Set.range U.U)
  let a : ℕ → IdF (sP Q).A := fun r => sFil Q (r : ℤ)
  have hanti : ∀ k l, k ≤ l → ∀ T, (a l).S T ≤ (a k).S T := fun k l h T => fil_anti q Q k l h T
  have htop : ∀ T : Q.FullSubcategory, (sFil Q 0).S T = ⊤ := fun T => T.obj.pdPow_zero
  have hqb : Function.Bijective (quoK q Q (s : ℤ) j) :=
    (toSq_bijective (sFil Q 0) (sFil Q (s : ℤ)) htop (fil_bot q s _) j).comp hbij
  have hgr : ∀ r, 0 ≤ r → r < s → 𝒮.P (CH.H (Pb.sq (a r) (a (r + 1))) j) := fun r _ hr =>
    gr_fin hSerre hAff hCech U s hs0 𝒮 h𝒮 r hr j
  have hP : 𝒮.P (CH.H (Pb.sq (a 0) (a s)) j) := dev 𝒮 a hanti s j 0 hgr s 0 le_rfl (by omega)
  have hfinH : Module.Finite K (HQ Q 0 (s : ℤ) j) := (h𝒮 _).1 hP
  refine ⟨Module.Finite.equiv (LinearEquiv.ofBijective (quoK q Q (s : ℤ) j) hqb).symm, ?_⟩
  have hgv : ∀ r, j + 1 ≤ r → r < s → (zeroSerre K).P (CH.H (Pb.sq (a r) (a (r + 1))) j) := fun r h0 hr =>
    gr_van hVan hAff U s r hr j h0
  have hz : Subsingleton (CH.H (Pb.sq (a (j + 1)) (a s)) j) :=
    dev (zeroSerre K) a hanti s j (j + 1) hgv (s - (j + 1)) (j + 1) le_rfl (by omega)
  intro x hx
  have h0 : quoK q Q ((j + 1 : ℕ) : ℤ) j x = 0 := (hfil (j + 1) hjs x).1 hx
  have hcb : ∀ T, (sFil Q (s : ℤ)).S T ≤ (sFil Q ((j + 1 : ℕ) : ℤ)).S T := fun T => fil_anti q Q (j + 1) s hjs T
  have hba : ∀ T, (sFil Q ((j + 1 : ℕ) : ℤ)).S T ≤ (sFil Q 0).S T := fun T => fil_anti q Q 0 (j + 1) (Nat.zero_le _) T
  have h1 : (sqLe (a := sFil Q 0) (b := sFil Q (s : ℤ)) (a' := sFil Q 0) (b' := sFil Q ((j + 1 : ℕ) : ℤ))
      (fun _ => le_rfl) hcb).pull j (quoK q Q (s : ℤ) j x) = 0 := by
    rw [← h0]
    exact toSq_comp (sFil Q 0) (sFil Q ((j + 1 : ℕ) : ℤ)) (sFil Q (s : ℤ)) htop hcb j (resK q Q j x)
  obtain ⟨w, hw⟩ := (sq_les (a := sFil Q 0) (b := sFil Q ((j + 1 : ℕ) : ℤ)) (c := sFil Q (s : ℤ)) hba hcb j _).1 h1
  have hw0 : w = 0 := hz.elim _ _
  rw [hw0, map_zero] at hw
  exact hqb.1 (by rw [← hw, map_zero])
