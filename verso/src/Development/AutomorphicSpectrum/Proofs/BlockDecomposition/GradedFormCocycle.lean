import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltration
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CocProd (tele sa_val)
open GlobalTheory.CompanionTheory.TowerEnd (Q dQ val Vals cl d_cl dQ_apply)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.Coc

local macro "fa" : tactic =>
  `(tactic| (simp only [sa_val, Fin.val_castSucc, Fin.val_succ, Fin.val_last, Fin.val_zero]; split_ifs <;> omega))

/- English proof (translation)
Use `set u : Fin j → B := fun k => w k k.succ.castSucc - w k k.castSucc.castSucc with hu`. Use `set v : Fin j → B := fun k => w k k.succ.succ - w k k.succ.castSucc with hv`. Use `set P : ℕ → B := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP`. Use `set T : Fin (j + 2) → B := fun i => ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) with hT`. Establish `cg : ∀ (k : Fin j) {p q p' q' : Fin (j + 2)}, (p : ℕ) = p' → (q : ℕ) = q' → w k p - w k q = w k p' - w k q'`.

Introduce `k p q p' q' h h'`. Rewrite using `[Fin.ext h, Fin.ext h']`. Establish `hT0 : T (Fin.castSucc 0) = P 0`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Nat.not_lt_zero, if_false]`.

Apply the tactic sequence `refine cg k ?_ ?_ <;> fa`. Establish `hTl : T (Fin.last (j + 1)) = P j`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [k.2, if_true]`. Apply the tactic sequence `refine cg k ?_ ?_ <;> fa`.

Establish `hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i`. Introduce `i`. Establish `hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k)`. Use `Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)` as an intermediate fact. Simplify using `only [Nat.lt_add_one, if_true] at this`.

Conclude with `this.symm`. Establish `hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k)`. Use `Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)` as an intermediate fact. Simplify using `only [lt_irrefl, if_false] at this`. Conclude with `this.symm`.

Establish `hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k)`. Use `Finset.mul_prod_erase Finset.univ (fun k : Fin j => w k (i.succ.castSucc.succAbove k.succ) - w k (i.succ.castSucc.succAbove k.castSucc)) (Finset.mem_univ i)` as an intermediate fact. Use `this.symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Establish `e : u i + v i = w i i.succ.succ - w i i.castSucc.castSucc`.

Rewrite using `[hu, hv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Apply the tactic sequence `refine cg i ?_ ?_ <;> fa`. Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations.

Establish `hki : (k : ℕ) ≠ i` using `fun h => Finset.ne_of_mem_erase hk (Fin.ext h)`. Use `split_ifs with h`. Apply the tactic sequence `refine cg k ?_ ?_ <;> fa`. Apply the tactic sequence `refine cg k ?_ ?_ <;> fa`. Establish `hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) = ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k)`.

Use `Finset.prod_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hki : (k : ℕ) ≠ i` using `fun h => Finset.ne_of_mem_erase hk (Fin.ext h)`. Establish `: (k : ℕ) < i + 1 ↔ (k : ℕ) < i` using `by omega`. Simplify using `only [this]`. Rewrite using `[hTa, hPa, hPb, hE]`.

Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) * T i = 0`. Rewrite using `[Fin.sum_univ_castSucc, Fin.sum_univ_succ]`. Establish `hint : ∑ i : Fin j, (-1 : B) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * T i.succ.castSucc = ∑ m ∈ Finset.range j, (-1 : B) ^ (m + 1) * (P (m + 1) + P m)`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun m => (-1 : B) ^ (m + 1) * (P (m + 1) + P m)) j]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hTi]`. Simplify using `only [Fin.val_castSucc, Fin.val_succ]`. Rewrite using `[hint, hT0, hTl]`. Simplify using `only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]`.

Take the linear combination `tele P j`.
-/
theorem alt_sum {B : Type*} [CommRing B] {j : ℕ} (w : Fin j → Fin (j + 2) → B) :
    ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) *
      ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) = 0 := by
  classical
  set u : Fin j → B := fun k => w k k.succ.castSucc - w k k.castSucc.castSucc with hu
  set v : Fin j → B := fun k => w k k.succ.succ - w k k.succ.castSucc with hv
  set P : ℕ → B := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → B := fun i =>
    ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) with hT
  have cg : ∀ (k : Fin j) {p q p' q' : Fin (j + 2)}, (p : ℕ) = p' → (q : ℕ) = q' →
      w k p - w k q = w k p' - w k q' := by
    intro k p q p' q' h h'
    rw [Fin.ext h, Fin.ext h']
  have hT0 : T (Fin.castSucc 0) = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine cg k ?_ ?_ <;> fa
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine cg k ?_ ?_ <;> fa
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => w k (i.succ.castSucc.succAbove k.succ) -
        w k (i.succ.castSucc.succAbove k.castSucc)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · have e : u i + v i = w i i.succ.succ - w i i.castSucc.castSucc := by
          rw [hu, hv]; ring
        rw [e]
        refine cg i ?_ ?_ <;> fa
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine cg k ?_ ?_ <;> fa
        · refine cg k ?_ ?_ <;> fa
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  change ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) * T i = 0
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hint : ∑ i : Fin j, (-1 : B) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * T i.succ.castSucc =
      ∑ m ∈ Finset.range j, (-1 : B) ^ (m + 1) * (P (m + 1) + P m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (-1 : B) ^ (m + 1) * (P (m + 1) + P m)) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hTi]
    simp only [Fin.val_castSucc, Fin.val_succ]
  rw [hint, hT0, hTl]
  simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
  linear_combination tele P j

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def vt (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last p)))).hom (c (s.obj p))

/- English proof (translation)
Substitute `hp` using the available equality. Establish `: (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _` using `Subsingleton.elim _ _`. Unfold `vt`. Rewrite using `[this, s.map_id]`. Simplify using the standard rewrite rules.
-/
theorem vt_last (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1))
    (hp : p = Fin.last n) : vt c s p = c (s.obj (Fin.last n)) := by
  subst hp
  have : (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ := Subsingleton.elim _ _
  unfold vt
  rw [this, s.map_id]
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem face_vt (c : ∀ T : C, Φ.A.obj T) {j : ℕ} (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (c ((face i s).obj (Fin.last j))) = vt c s (i.succAbove (Fin.last j)) := rfl

/- English proof (translation)
Unfold `wz`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.CocProd.map_map]`. Establish `e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s = s.map (homOfLE (Fin.le_last (i.succAbove k.succ)))`.

Express the relevant statement in the definitionally equal form `s.map _ ≫ s.map _ = _`. Rewrite using `[← s.map_comp]`. Both sides reduce to the same expression. Rewrite using `[e, map_sub, GlobalTheory.CompanionTheory.CocProd.map_map]`. Establish `e2 : (face i s).map (homOfLE (Fin.castSucc_lt_succ (i` using `k)).le) ≫ s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) = s.map (homOfLE (Fin.le_last (i.succAbove k.castSucc))) := by`.

Express the relevant statement in the definitionally equal form `s.map _ ≫ s.map _ = _`. Rewrite using `[← s.map_comp]`. Both sides reduce to the same expression. Rewrite using `[e2]`. Both sides reduce to the same expression.
-/
theorem face_wz {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T) (I : Fin j → Fin d)
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (wz u I (face i s)) =
      ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) := by
  unfold wz
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [GlobalTheory.CompanionTheory.CocProd.map_map]
  have e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e, map_sub, GlobalTheory.CompanionTheory.CocProd.map_map]
  have e2 : (face i s).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le) ≫
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) =
      s.map (homOfLE (Fin.le_last (i.succAbove k.castSucc))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e2]
  rfl

/- English proof (translation)
Use `set Y := y (s.obj (Fin.last (j + 1))) with hY`. Use `set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i => ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) with hT`. Use `set V : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i => vt y s (i.succAbove (Fin.last j)) with hV`. Establish `hVY : ∀ i : Fin (j + 1), V i.castSucc = Y`. Introduce `i`.

Use `vt_last y s _ (Fin.ext ?_)` and prove the remaining obligations. Use `i.2` as an intermediate fact. Rewrite using `[sa_val]`. Simplify using `only [Fin.val_last, Fin.val_castSucc]`. Apply the tactic sequence `split_ifs <;> omega`.

Establish `hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (wz u I (face i s) * y ((face i s).obj (Fin.last j))) = (-1) ^ j * (T (Fin.last (j + 1)) * (Y - V (Fin.last (j + 1))))`. Establish `hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom (wz u I (face i s) * y ((face i s).obj (Fin.last j))) = (-1) ^ (i : ℕ) * (T i * V i)`. Introduce `i`. Rewrite using `[map_mul, face_wz, face_vt, zsmul_eq_mul]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `h0` using `alt_sum (B := Φ.A.obj (s.obj (Fin.last (j + 1)))) (j := j) (fun k p => vt (u (I k)) s p)`. Express the relevant statement in the definitionally equal form `∑ i : Fin (j + 2), (-1) ^ (i : ℕ) * T i = 0 at h0`. Rewrite `h0` using `[Fin.sum_univ_castSucc]`. Rewrite using `[Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc]`.

Establish `h1 : ∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * (T i.castSucc * V i.castSucc) = (∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * T i.castSucc) * Y`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hVY]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Simplify using `only [Fin.val_last] at h0 ⊢`. Take the linear combination `Y * h0`. Rewrite using `[hsum]`. Use `Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations.

Establish `hA : T (Fin.last (j + 1)) ∈ (Fil (j : ℤ)).S _`. Use `(Fil (j : ℤ)).map_mem (toLast (Fin.last (j + 1)) s) (wz_mem hF u hu I (face (Fin.last (j + 1)) s))` as an intermediate fact. Rewrite `this` using `[face_wz]`. Then use the resulting hypothesis. Establish `hB : Y - V (Fin.last (j + 1)) ∈ (Fil ((1 : ℕ) : ℤ)).S _`. Establish `e : (((1 : ℕ) : ℤ)) = 1` using `rfl`.

Rewrite using `[e, hF.one]`. Establish `h` using `hy (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))`. Establish `e2 : V (Fin.last (j + 1)) = (Φ.A.map (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))).hom (y (s.obj (Fin.last j).castSucc))`. Establish `: (Fin.last (j + 1)).succAbove (Fin.last j) = (Fin.last j).castSucc` using `Fin.succAbove_last_apply _`. Simplify using `only [hV, vt]`.

Rewrite using `[this]`. Rewrite using `[e2]`. Conclude with `h`. Establish `h` using `hF.mul j 1 _ hA hB`. Establish `e : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1` using `by push_cast; ring`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem d_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (y : ∀ T : C, Φ.A.obj T) (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (Φ.A.map φ).hom (y T) ∈ Φ.J.S T')
    (I : Fin j → Fin d) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) ∈ (Fil ((j : ℤ) + 1)).S _ := by
  set Y := y (s.obj (Fin.last (j + 1))) with hY
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) with hT
  set V : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    vt y s (i.succAbove (Fin.last j)) with hV
  have hVY : ∀ i : Fin (j + 1), V i.castSucc = Y := by
    intro i
    refine vt_last y s _ (Fin.ext ?_)
    have := i.2
    rw [sa_val]
    simp only [Fin.val_last, Fin.val_castSucc]
    split_ifs <;> omega
  have hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) =
      (-1) ^ j * (T (Fin.last (j + 1)) * (Y - V (Fin.last (j + 1)))) := by
    have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
        (wz u I (face i s) * y ((face i s).obj (Fin.last j))) = (-1) ^ (i : ℕ) * (T i * V i) := by
      intro i
      rw [map_mul, face_wz, face_vt, zsmul_eq_mul]
      push_cast
      rfl
    have h0 := alt_sum (B := Φ.A.obj (s.obj (Fin.last (j + 1)))) (j := j) (fun k p => vt (u (I k)) s p)
    change ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) * T i = 0 at h0
    rw [Fin.sum_univ_castSucc] at h0
    rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc]
    have h1 : ∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * (T i.castSucc * V i.castSucc) =
        (∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * T i.castSucc) * Y := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hVY]
      ring
    rw [h1]
    simp only [Fin.val_last] at h0 ⊢
    linear_combination Y * h0
  rw [hsum]
  refine Ideal.mul_mem_left _ _ ?_
  have hA : T (Fin.last (j + 1)) ∈ (Fil (j : ℤ)).S _ := by
    have := (Fil (j : ℤ)).map_mem (toLast (Fin.last (j + 1)) s) (wz_mem hF u hu I (face (Fin.last (j + 1)) s))
    rwa [face_wz] at this
  have hB : Y - V (Fin.last (j + 1)) ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    have e : (((1 : ℕ) : ℤ)) = 1 := rfl
    rw [e, hF.one]
    have h := hy (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))
    have e2 : V (Fin.last (j + 1)) = (Φ.A.map (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))).hom
        (y (s.obj (Fin.last j).castSucc)) := by
      have : (Fin.last (j + 1)).succAbove (Fin.last j) = (Fin.last j).castSucc := Fin.succAbove_last_apply _
      simp only [hV, vt]
      rw [this]
    rw [e2]
    exact h
  have h := hF.mul j 1 _ hA hB
  have e : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  rwa [e] at h

end GlobalTheory.CompanionTheory.GrForm.Coc

open GlobalTheory.CompanionTheory.GrForm.Coc in

/- English proof (translation)
Introduce `R _ C _ Φ Fil hF d j u hu y hy I`. Set `z : Q Φ.A j` to `fun s => (wz u I s * y (s.obj (Fin.last j)) : Φ.A.obj (s.obj (Fin.last j)))`. Establish `hz : Vals (Fil j) z` using `fun s => Ideal.mul_mem_right _ _ (wz_mem hF u hu I s)`. Use `⟨cl (Fil j) (Fil ((j : ℤ) + 1)) z hz, ?_, fun s => rfl⟩` and prove the remaining obligations. Rewrite using `[d_cl]`.

Use function extensionality and compare the values at `s`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (val (dQ Φ.A j z) s) = 0`. Rewrite using `[dQ_apply]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (d_mem hF u hu y hy I s)`.
-/
theorem GlobalTheory.CompanionTheory.GrForm.stCocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  intro R _ C _ Φ Fil hF d j u hu y hy I
  let z : Q Φ.A j := fun s => (wz u I s * y (s.obj (Fin.last j)) : Φ.A.obj (s.obj (Fin.last j)))
  have hz : Vals (Fil j) z := fun s => Ideal.mul_mem_right _ _ (wz_mem hF u hu I s)
  refine ⟨cl (Fil j) (Fil ((j : ℤ) + 1)) z hz, ?_, fun s => rfl⟩
  rw [d_cl]
  funext s
  apply Subtype.ext
  change Ideal.Quotient.mk _ (val (dQ Φ.A j z) s) = 0
  rw [dQ_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (d_mem hF u hu y hy I s)
