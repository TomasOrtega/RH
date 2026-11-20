import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.CosetCount

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.StandardBlocks

/- English proof (translation)
Establish `hi : (i : ℕ) = 0`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[stdBlocks_val]`.

Simplify using `[hi]`.
-/
theorem stdBlocks_one {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) (a : Fin n) (i : Fin 1) :
    stdBlocks (fun _ : Fin n => 1) hd ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [hi]

/- English proof (translation)
Take `⟨⟨a, p⟩, rfl⟩` from `(stdBlocks (fun _ : Fin n => 1) hd).surjective i`. Rewrite using `[blk_apply]`. Conclude with `(stdBlocks_one hd a p).symm`.
-/
theorem blk_stdBlocks {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) (i : Fin n) :
    blk (stdBlocks (fun _ : Fin n => 1) hd) i = i := by
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective i
  rw [blk_apply]
  exact (stdBlocks_one hd a p).symm

/- English proof (translation)
Establish `hb2 : ∀ i : Fin n, blk (points (Fin n)) i = i` using `fun i => by`. Establish `h` using `blk_apply (points (Fin n)) i ()`. Rewrite `h` using `[points_apply]`. Then use the resulting hypothesis. Use extensionality with `g`. Rewrite using `[unipB, mem_unipRad, mem_unipRad, mem_parab, mem_parab]`.

Simplify using `only [blk_stdBlocks, hb2]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, fun a i j => ?_⟩` and prove the remaining obligations. Establish `h` using `h2 a (0 : Fin 1) (0 : Fin 1)`.

Simplify using `only [stdBlocks_one] at h`. Simplify using `only [points_apply]`. Rewrite using `[h]`. Simplify using `[Matrix.one_apply]`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨h1, fun a i j => ?_⟩` and prove the remaining obligations. Establish `h` using `h2 a () ()`. Simplify using `only [points_apply] at h`. Simplify using `only [stdBlocks_one]`. Take `rfl : i = j` from `Subsingleton.elim i j`.

Rewrite using `[h]`. Simplify using `[Matrix.one_apply]`.
-/
theorem unipRad_stdBlocks (k : Type) [Field k] {n : ℕ} (hd : ∑ _a : Fin n, 1 = n) :
    unipRad k (stdBlocks (fun _ : Fin n => 1) hd) = unipB k (Fin n) := by
  have hb2 : ∀ i : Fin n, blk (points (Fin n)) i = i := fun i => by
    have h := blk_apply (points (Fin n)) i ()
    rwa [points_apply] at h
  ext g
  rw [unipB, mem_unipRad, mem_unipRad, mem_parab, mem_parab]
  simp only [blk_stdBlocks, hb2]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a i j => ?_⟩
    have h := h2 a (0 : Fin 1) (0 : Fin 1)
    simp only [stdBlocks_one] at h
    simp only [points_apply]
    rw [h]
    simp [Matrix.one_apply]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun a i j => ?_⟩
    have h := h2 a () ()
    simp only [points_apply] at h
    simp only [stdBlocks_one]
    obtain rfl : i = j := Subsingleton.elim i j
    rw [h]
    simp [Matrix.one_apply]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Take `⟨⟨a, p⟩, rfl⟩` from `(stdBlocks (fun _ : Fin n => 1) hd).surjective i`. Take `⟨⟨b, q⟩, rfl⟩` from `(stdBlocks (fun _ : Fin n => 1) hd).surjective j`. Rewrite using `[val_diagT]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Establish `hpq : p = q` using `Subsingleton.elim _ _`. Substitute `hpq` using the available equality. Rewrite using `[leviEmb_apply_same, stdBlocks_one]`.

Simplify using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, Subsingleton.elim p 0]`. Rewrite using `[leviEmb_apply_ne k _ t hab, stdBlocks_one, stdBlocks_one, Matrix.diagonal_apply_ne _ hab]`.
-/
theorem leviEmb_stdBlocks (k : Type) [Field k] {n : ℕ} (hd : ∑ _a : Fin n, 1 = n)
    (t : Levi k fun _ : Fin n => Fin 1) :
    leviEmb k (stdBlocks (fun _ : Fin n => 1) hd) t =
      diagT k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a) := by
  apply Units.ext
  ext i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (fun _ : Fin n => 1) hd).surjective j
  rw [val_diagT]
  by_cases hab : a = b
  · subst hab
    have hpq : p = q := Subsingleton.elim _ _
    subst hpq
    rw [leviEmb_apply_same, stdBlocks_one]
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one, Subsingleton.elim p 0]
  · rw [leviEmb_apply_ne k _ t hab, stdBlocks_one, stdBlocks_one, Matrix.diagonal_apply_ne _ hab]

/- English proof (translation)
Rewrite using `[deltaHalf_apply, deltaHalf_apply]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[modExp_fin (fun _ : Fin n => Fin 1) (fun _ => Fintype.card_fin 1) a, modExp_fin (fun _ : Fin n => Unit) (fun _ => Fintype.card_unit) a]`. Use `congr 1`. Conclude with `(congrFun ((leviTorus k (Fin n)).symm_apply_apply fun a => Matrix.GeneralLinearGroup.det (t a)) a).symm`.
-/
theorem deltaHalf_stdBlocks (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Levi k fun _ : Fin n => Fin 1) :
    deltaHalf k (fun _ : Fin n => Fin 1) t =
      deltaHalf k (fun _ : Fin n => Unit)
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [modExp_fin (fun _ : Fin n => Fin 1) (fun _ => Fintype.card_fin 1) a,
    modExp_fin (fun _ : Fin n => Unit) (fun _ => Fintype.card_unit) a]
  congr 1
  exact (congrFun ((leviTorus k (Fin n)).symm_apply_apply
    fun a => Matrix.GeneralLinearGroup.det (t a)) a).symm

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem twKer_one_congr {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) {N N' : Subgroup G} (h : N = N') : twKer π N 1 = twKer π N' 1 := by
  subst h
  rfl

/- English proof (translation)
Rewrite using `[PositivityTheory.Lbc.torusChar, GlobalTheory.SmGL.torusChar, MonoidHom.finsetProd_apply, Units.coe_prod]`. Both sides reduce to the same expression.
-/
theorem torusChar_stdBlocks {k : Type} [Field k] {n : ℕ} (χ : Fin n → kˣ →* ℂˣ)
    (t : ∀ _ : Fin n, GL (Fin 1) k) :
    PositivityTheory.Lbc.torusChar χ t =
      (torusChar χ (fun a => Matrix.GeneralLinearGroup.det (t a)) : ℂ) := by
  rw [PositivityTheory.Lbc.torusChar, GlobalTheory.SmGL.torusChar, MonoidHom.finsetProd_apply, Units.coe_prod]
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `hk`.
-/
private theorem smul_mk_eq_smul_mk_of_submodule_eq {V : Type} [AddCommGroup V] [Module ℂ V]
    {p q : Submodule ℂ V} (h : p = q) (a b : ℂ) (u w : V)
    (hk : a • (Submodule.Quotient.mk u : V ⧸ p) = b • Submodule.Quotient.mk w) :
    a • (Submodule.Quotient.mk u : V ⧸ q) = b • Submodule.Quotient.mk w := by
  subst h
  exact hk

/- English proof (translation)
Introduce `k _ _ _ _ n hd V _ _ π χ y hy heig`. Establish `hK : twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 = twKer π (unipRad k (points (Fin n))) 1` using `twKer_one_congr π (unipRad_stdBlocks k hd)`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective (twKer π (unipRad k (points (Fin n))) 1) y`. Use `⟨(Submodule.Quotient.mk w : V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1), ?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hy` to reduce the goal to its premises. Establish `h' : w ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1` using `(Submodule.Quotient.mk_eq_zero _).mp h`. Rewrite `h'` using `[hK]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).mpr h'`. Introduce `t`.

Establish `key : (jac (points (Fin n)) π (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a))) (Submodule.Quotient.mk w) = ((torusChar χ fun a => Matrix.GeneralLinearGroup.det (t a) : ℂˣ) : ℂ) • Submodule.Quotient.mk w` using `heig (fun a => Matrix.GeneralLinearGroup.det (t a))`. Establish `hD : leviEmb k (points (Fin n)) (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) = diagT k (Fin n) (fun a => Matrix.GeneralLinearGroup.det (t a))` using `rfl`. Rewrite `key` using `[jac_mk, hD]`. Establish `heq : (jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (Submodule.Quotient.mk w) = PositivityTheory.Lbc.torusChar χ t • (Submodule.Quotient.mk w : V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1)`. Rewrite using `[jac_mk, leviEmb_stdBlocks, deltaHalf_stdBlocks, torusChar_stdBlocks]`.

Conclude with `smul_mk_eq_smul_mk_of_submodule_eq hK.symm _ _ _ _ key`. Rewrite using `[Module.End.mem_maxGenEigenspace]`. Use `⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `heq`.
-/
theorem stdBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.StdBridge := by
  intro k _ _ _ _ n hd V _ _ π χ y hy heig
  have hK : twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 =
      twKer π (unipRad k (points (Fin n))) 1 :=
    twKer_one_congr π (unipRad_stdBlocks k hd)
  obtain ⟨w, rfl⟩ :=
    Submodule.Quotient.mk_surjective (twKer π (unipRad k (points (Fin n))) 1) y
  refine ⟨(Submodule.Quotient.mk w :
    V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1), ?_, ?_⟩
  · intro h
    apply hy
    have h' : w ∈ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1 :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    rw [hK] at h'
    exact (Submodule.Quotient.mk_eq_zero _).mpr h'
  · intro t
    have key : (jac (points (Fin n)) π
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)))
          (Submodule.Quotient.mk w) =
        ((torusChar χ fun a => Matrix.GeneralLinearGroup.det (t a) : ℂˣ) : ℂ) •
          Submodule.Quotient.mk w :=
      heig (fun a => Matrix.GeneralLinearGroup.det (t a))
    have hD : leviEmb k (points (Fin n))
        (leviTorus k (Fin n) fun a => Matrix.GeneralLinearGroup.det (t a)) =
        diagT k (Fin n) (fun a => Matrix.GeneralLinearGroup.det (t a)) := rfl
    rw [jac_mk, hD] at key
    have heq : (jac (stdBlocks (fun _ : Fin n => 1) hd) π t) (Submodule.Quotient.mk w) =
        PositivityTheory.Lbc.torusChar χ t • (Submodule.Quotient.mk w :
          V ⧸ twKer π (unipRad k (stdBlocks (fun _ : Fin n => 1) hd)) 1) := by
      rw [jac_mk, leviEmb_stdBlocks, deltaHalf_stdBlocks, torusChar_stdBlocks]
      exact smul_mk_eq_smul_mk_of_submodule_eq hK.symm _ _ _ _ key
    rw [Module.End.mem_maxGenEigenspace]
    refine ⟨1, ?_⟩
    rw [pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact heq

end GlobalTheory.CompanionTheory.StandardBlocks

end
