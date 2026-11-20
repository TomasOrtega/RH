import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.CompanionTheory.Hodge.Nerve

namespace GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]

/- English proof (translation)
The claim follows from `CategoryTheory.Functor.ext h (fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _))`.
-/
theorem chain_ext {n : ℕ} {c c' : Fin (n + 1) ⥤ Pᵒᵖ} (h : ∀ i, c.obj i = c'.obj i) : c = c' :=
  CategoryTheory.Functor.ext h (fun _ _ _ => Quiver.Hom.unop_inj (Subsingleton.elim _ _))

/- English proof (translation)
The claim follows from `leOfHom (c.map (homOfLE h)).unop`.
-/
theorem chain_anti {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {i j : Fin (n + 1)} (h : i ≤ j) :
    (c.obj j).unop ≤ (c.obj i).unop :=
  leOfHom (c.map (homOfLE h)).unop

def snocObj {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) : Fin (n + 2) → Pᵒᵖ :=
  Fin.snoc (α := fun _ ↦ Pᵒᵖ) (fun i ↦ c.obj i) (op b)

/- English proof (translation)
The claim follows from `Fin.snoc_last (α := fun _ ↦ Pᵒᵖ) _ _`.
-/
@[simp] theorem snocObj_last {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) :
    snocObj c b (Fin.last _) = op b :=
  Fin.snoc_last (α := fun _ ↦ Pᵒᵖ) _ _

/- English proof (translation)
The claim follows from `Fin.snoc_castSucc (α := fun _ ↦ Pᵒᵖ) _ _ _`.
-/
@[simp] theorem snocObj_castSucc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (i : Fin (n + 1)) :
    snocObj c b i.castSucc = c.obj i :=
  Fin.snoc_castSucc (α := fun _ ↦ Pᵒᵖ) _ _ _

/- English proof (translation)
Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Rewrite using `[GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact le_of_eq (by rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last])`.

Consider the case `cast i`. Rewrite using `[GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]`. Conclude with `hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last i))`. Consider the case `cast j`. Rewrite using `[GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]`.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact absurd h (not_le.mpr (Fin.castSucc_lt_last j))`. Consider the case `cast i`. Rewrite using `[GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]`. Conclude with `GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.castSucc_le_castSucc_iff.mp h)`.
-/
theorem snocObj_anti {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {b : P} (hb : b ≤ (c.obj (Fin.last n)).unop)
    {i j : Fin (n + 2)} (h : i ≤ j) : (snocObj c b j).unop ≤ (snocObj c b i).unop := by
  induction j using Fin.lastCases with
  | last =>
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]
    induction i using Fin.lastCases with
    | last => exact le_of_eq (by rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last])
    | cast i =>
      rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
      exact hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last i))
  | cast j =>
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
    induction i using Fin.lastCases with
    | last => exact absurd h (not_le.mpr (Fin.castSucc_lt_last j))
    | cast i =>
      rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
      exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.castSucc_le_castSucc_iff.mp h)

def snoc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (hb : b ≤ (c.obj (Fin.last n)).unop) :
    Fin (n + 2) ⥤ Pᵒᵖ where
  obj := snocObj c b
  map h := (homOfLE (snocObj_anti c hb (leOfHom h))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/- English proof (translation)
The claim follows from `le_of_eq (congrArg Opposite.unop (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last c b)).symm`.
-/
theorem snoc_last_le {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P) (hb : b ≤ (c.obj (Fin.last n)).unop) :
    b ≤ ((snoc c b hb).obj (Fin.last _)).unop :=
  le_of_eq (congrArg Opposite.unop (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last c b)).symm

abbrev face {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) : Fin (n + 1) ⥤ Pᵒᵖ :=
  (Fin.succAboveOrderEmb i).toOrderHom.monotone.functor ⋙ c

/- English proof (translation)
The claim follows from `hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last _))`.
-/
theorem face_le {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) : b ≤ ((face i c).obj (Fin.last _)).unop :=
  hb.trans (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_anti c (Fin.le_last _))

/- English proof (translation)
Apply `GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext` to reduce the goal to its premises. Introduce `k`. Proceed by induction on `k using Fin.lastCases with`. Consider the case `last => show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.last _)) = GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.last _)`. Rewrite using `[Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i)), Fin.succ_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]`.

Consider the case `cast k => show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.castSucc k)) = GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.castSucc k)`. Rewrite using `[Fin.castSucc_succAbove_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]`. Apply the tactic sequence `all_goals rfl`.
-/
theorem face_castSucc_snoc {n : ℕ} (i : Fin (n + 2)) (c : Fin (n + 2) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) :
    face i.castSucc (snoc c b hb) = snoc (face i c) b (face_le i c hb) := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext
  intro k
  induction k using Fin.lastCases with
  | last =>
    show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.last _)) =
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.last _)
    rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i)),
      Fin.succ_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_last]
  | cast k =>
    show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.castSucc i).succAbove (Fin.castSucc k)) =
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (Fin.castSucc k)
    rw [Fin.castSucc_succAbove_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]
    all_goals rfl

/- English proof (translation)
Apply `GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext` to reduce the goal to its premises. Introduce `k`. Use `show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.last _).succAbove k) = c.obj k`. Rewrite using `[Fin.succAbove_last_apply, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]`.
-/
theorem face_last_snoc {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) {b : P}
    (hb : b ≤ (c.obj (Fin.last _)).unop) : face (Fin.last _) (snoc c b hb) = c := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.chain_ext
  intro k
  show GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj c b ((Fin.last _).succAbove k) = c.obj k
  rw [Fin.succAbove_last_apply, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snocObj_castSucc]

def valL (M : P → ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) : NC (coind M) n →ₗ[R] M b where
  toFun f := f c ⟨b, hb⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem valL_congr (M : P → ModuleCat.{0} R) {n : ℕ} {c c' : Fin (n + 1) ⥤ Pᵒᵖ} (h : c = c') (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) (hb' : b ≤ (c'.obj (Fin.last n)).unop) (f : NC (coind M) n) :
    valL M c b hb f = valL M c' b hb' f := by
  subst h
  rfl

/- English proof (translation)
Use `first`. Consider the case `(simp only [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]; all_goals exact Finset.sum_congr rfl fun i _ => rfl)`. Consider the case `(rw [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, map_sum];`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply, map_smul]; rfl)`.
-/
theorem valL_dNC (M : P → ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 2) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last _)).unop) (f : NC (coind M) n) :
    valL M c b hb (dNC (coind M) n f) =
      ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • valL M (face i c) b (face_le i c hb) f := by
  first
    | (simp only [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul];
        all_goals exact Finset.sum_congr rfl fun i _ => rfl)
    | (rw [GlobalTheory.CompanionTheory.Hodge.Nerve.dNC, LinearMap.sum_apply, map_sum];
        exact Finset.sum_congr rfl fun i _ => by rw [LinearMap.smul_apply, map_smul]; rfl)

def contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1)) : NC (coind M) n :=
  fun c b ↦ valL M (snoc c b.1 b.2) b.1 (snoc_last_le c b.1 b.2) f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valL_contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1)) (c : Fin (n + 1) ⥤ Pᵒᵖ) (b : P)
    (hb : b ≤ (c.obj (Fin.last n)).unop) :
    valL M c b hb (contr M f) = valL M (snoc c b hb) b (snoc_last_le c b hb) f := rfl

/- English proof (translation)
Use function extensionality and compare the values at `c b`. Conclude with `h c b.1 b.2`.
-/
theorem NC_ext (M : P → ModuleCat.{0} R) {n : ℕ} {f g : NC (coind M) n}
    (h : ∀ c b hb, valL M c b hb f = valL M c b hb g) : f = g := by
  funext c b
  exact h c b.1 b.2

/- English proof (translation)
Apply `GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.NC_ext` to reduce the goal to its premises. Introduce `c b hb`. Establish `hcoc : GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc c b hb) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc_last_le c b hb) (GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.co …`. Rewrite using `[hf, map_zero]`. Rewrite `hcoc` using `[GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, Fin.sum_univ_castSucc]`.

Establish `hsum : ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_le i c hb) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M f) …`. Rewrite using `[eq_neg_iff_add_eq_zero, ← hcoc]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.val_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_contr]`.

Conclude with `congrArg ((-1 : R) ^ (i : ℕ) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_castSucc_snoc i c hb).symm b _ _ f)`. Rewrite using `[Fin.val_last]`. Conclude with `congrArg ((-1 : R) ^ (n + 1 + 1) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_last_snoc c hb).symm b _ _ f)`. Establish `hp : (-1 : R) ^ (n + 1) * (-1 : R) ^ (n + 1) = 1`. Rewrite using `[← mul_pow, neg_one_mul, neg_neg, one_pow]`.

Rewrite using `[map_smul, map_smul, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, hsum, smul_neg, smul_smul, pow_succ (-1 : R) (n + 1), ← mul_assoc, hp, one_mul, neg_smul, one_smul, neg_neg]`.
-/
theorem dNC_contr (M : P → ModuleCat.{0} R) {n : ℕ} (f : NC (coind M) (n + 1))
    (hf : dNC (coind M) (n + 1) f = 0) :
    dNC (coind M) n (((-1 : R) ^ (n + 1)) • contr M f) = f := by
  apply GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.NC_ext
  intro c b hb
  have hcoc : GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc c b hb) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.snoc_last_le c b hb)
      (GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) f) = 0 := by
    rw [hf, map_zero]
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, Fin.sum_univ_castSucc] at hcoc
  have hsum : ∑ i : Fin (n + 2), (-1 : R) ^ (i : ℕ) •
      GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face i c) b (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_le i c hb)
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M f) =
      -((-1 : R) ^ (n + 1 + 1) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL M c b hb f) := by
    rw [eq_neg_iff_add_eq_zero, ← hcoc]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.val_castSucc, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_contr]
      exact congrArg ((-1 : R) ^ (i : ℕ) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_castSucc_snoc i c hb).symm b _ _ f)
    · rw [Fin.val_last]
      exact congrArg ((-1 : R) ^ (n + 1 + 1) • ·) (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_congr M
        (GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.face_last_snoc c hb).symm b _ _ f)
  have hp : (-1 : R) ^ (n + 1) * (-1 : R) ^ (n + 1) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [map_smul, map_smul, GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.valL_dNC, hsum, smul_neg, smul_smul,
    pow_succ (-1 : R) (n + 1), ← mul_assoc, hp, one_mul, neg_smul, one_smul, neg_neg]

end GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc

open GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc in

/- English proof (translation)
Rewrite using `[← HomologicalComplex.exactAt_iff_isZero_homology, HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp), ShortComplex.moduleCat_exact_iff]`. Introduce `x hx`. Establish `hx' : GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) x = 0`. Express the relevant statement in the definitionally equal form `((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d (n + 1) (n + 1 + 1)).hom x = 0 at hx`. Rewrite `hx` using `[GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d]`.

Conclude with `hx`. Use `⟨((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d n (n + 1)).hom (((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x) = x`. Rewrite using `[GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d]`. Conclude with `GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.dNC_contr M x hx'`.
-/
theorem GlobalTheory.CompanionTheory.Hodge.Nerve.isZero_homology_coind {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
    (M : P → ModuleCat.{0} R) (n : ℕ) : IsZero ((nerveCx.obj (coind M)).homology (n + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 1 + 1) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : GlobalTheory.CompanionTheory.Hodge.Nerve.dNC (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M) (n + 1) x = 0 := by
    change ((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d (n + 1) (n + 1 + 1)).hom x = 0 at hx
    rw [GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d] at hx
    exact hx
  refine ⟨((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x, ?_⟩
  change ((GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx.obj (GlobalTheory.CompanionTheory.Hodge.Nerve.coind M)).d n (n + 1)).hom
    (((-1 : R) ^ (n + 1)) • GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.contr M x) = x
  rw [GlobalTheory.CompanionTheory.Hodge.Nerve.nerveCx_d]
  exact GlobalTheory.CompanionTheory.Hodge.Nerve.Acyc.dNC_contr M x hx'
