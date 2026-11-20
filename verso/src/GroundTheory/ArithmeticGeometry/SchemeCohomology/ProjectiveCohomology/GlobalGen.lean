import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheafAlt
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Generation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
  MvPolynomial

universe w' u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

section Res

variable {X : Scheme.{u}}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(F.presheaf.map (homOfLE h).op).hom m = m`. Rewrite using `[show (homOfLE h).op = 𝟙 (op U) from rfl, F.presheaf.map_id]`. Both sides reduce to the same expression.
-/
private lemma resF_refl (F : X.Modules) {U : X.Opens} (h : U ≤ U) (m : Γ(F, U)) : resF F h m = m := by
  change (F.presheaf.map (homOfLE h).op).hom m = m
  rw [show (homOfLE h).op = 𝟙 (op U) from rfl, F.presheaf.map_id]
  rfl

/- English proof (translation)
Introduce `a b hab` and use `by have := congrArg (resF F h') hab rwa [resF_resF, resF_resF, resF_refl, resF_refl] at this`.
-/
private lemma resF_injective_of_le (F : X.Modules) {U V : X.Opens} (h : V ≤ U) (h' : U ≤ V) :
    Function.Injective (resF F h) := fun a b hab => by
  have := congrArg (resF F h') hab
  rwa [resF_resF, resF_resF, resF_refl, resF_refl] at this

end Res

namespace ProjSpace

variable {A : Type u} [CommRing A] {n : ℕ}

private abbrev yR (k j : Fin (n + 1)) : Γ(projectiveSpace A n, stdOpen A n k) :=
  ProjTwist.ratio (grading A n) (X_mem k) (X_mem j)

private def upowS (k : Fin (n + 1)) (m : ℤ) :
    ((preMod (projectiveSpace A n)).obj (twistingSheaf (grading A n) m)).obj (op (stdOpen A n k)) :=
  ProjTwist.upow (grading A n) (X_mem k) m

/- English proof (translation)
The claim follows from `ProjTwist.upow_res _ _ m`.
-/
private lemma upowS_res (k l : Fin (n + 1)) (m : ℕ) :
    resM ((preMod (projectiveSpace A n)).obj (twistingSheaf (grading A n) m))
        (inf_le_right : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n l) (upowS l m) =
      resR (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR (A := A) k l) ^ m •
        resM ((preMod (projectiveSpace A n)).obj (twistingSheaf (grading A n) m))
          (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (upowS k m) :=
  ProjTwist.upow_res _ _ m

/- English proof (translation)
The claim follows from `ProjTwist.basicOpen_ratio _ _`.
-/
private lemma basicOpen_yR (k j : Fin (n + 1)) :
    (projectiveSpace A n).basicOpen (yR (A := A) k j) = stdOpen A n k ⊓ stdOpen A n j :=
  ProjTwist.basicOpen_ratio _ _

/- English proof (translation)
Establish `e : stdOpen A n k ⊓ stdOpen A n l = Proj.basicOpen (grading A n) (X k * X l)` using `(Proj.basicOpen_mul _ _ _).symm`. Rewrite using `[e]`. Conclude with `Proj.isAffineOpen_basicOpen _ _ (SetLike.mul_mem_graded (X_mem k) (X_mem l)) two_pos`.
-/
private lemma isAffineOpen_stdOpen_inf (k l : Fin (n + 1)) :
    IsAffineOpen (stdOpen A n k ⊓ stdOpen A n l) := by
  have e : stdOpen A n k ⊓ stdOpen A n l = Proj.basicOpen (grading A n) (X k * X l) :=
    (Proj.basicOpen_mul _ _ _).symm
  rw [e]
  exact Proj.isAffineOpen_basicOpen _ _ (SetLike.mul_mem_graded (X_mem k) (X_mem l)) two_pos

/- English proof (translation)
Establish `hb` using `basicOpen_yR (A := A) k j`. Establish `hle : (projectiveSpace A n).basicOpen (yR (A` using `A) k j) ≤ stdOpen A n j := hb.le.trans inf_le_right`. Take `⟨e, g, hg⟩` from `qcoh_exists_res_eq G (isAffineOpen_stdOpen k) (yR k j) (resF G hle s)`. Use `⟨e, g, ?_⟩` and prove the remaining obligations. Establish `h2 : stdOpen A n k ⊓ stdOpen A n j ≤ (projectiveSpace A n).basicOpen (yR (A` using `A) k j) := hb.ge`.

Use `congrArg (resF G h2) hg` as an intermediate fact. Rewrite `this` using `[resF_resF, resF_smul, map_pow, resO_resO, resF_resF]`. Conclude with `this`.
-/
private lemma exists_local (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] (j : Fin (n + 1))
    (s : Γ(G, stdOpen A n j)) (k : Fin (n + 1)) :
    ∃ (e : ℕ) (g : Γ(G, stdOpen A n k)),
      resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) g =
        resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (yR k j) ^ e •
          resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n j) s := by
  have hb := basicOpen_yR (A := A) k j
  have hle : (projectiveSpace A n).basicOpen (yR (A := A) k j) ≤ stdOpen A n j :=
    hb.le.trans inf_le_right
  obtain ⟨e, g, hg⟩ := qcoh_exists_res_eq G (isAffineOpen_stdOpen k) (yR k j) (resF G hle s)
  refine ⟨e, g, ?_⟩
  have h2 : stdOpen A n k ⊓ stdOpen A n j ≤ (projectiveSpace A n).basicOpen (yR (A := A) k j) :=
    hb.ge
  have := congrArg (resF G h2) hg
  rw [resF_resF, resF_smul, map_pow, resO_resO, resF_resF] at this
  exact this

/- English proof (translation)
Use `choose e g hg using exists_local G j s`. Use `⟨Finset.univ.sup e, fun k => yR (A := A) k j ^ (Finset.univ.sup e - e k) • g k, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[resF_smul, hg, smul_smul, map_pow, ← pow_add, Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ k))]`.
-/
private lemma exists_local_uniform (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent]
    (j : Fin (n + 1)) (s : Γ(G, stdOpen A n j)) :
    ∃ (a : ℕ) (g : ∀ k, Γ(G, stdOpen A n k)), ∀ k,
      resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (g k) =
        resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (yR k j) ^ a •
          resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n j) s := by
  choose e g hg using exists_local G j s
  refine ⟨Finset.univ.sup e, fun k => yR (A := A) k j ^ (Finset.univ.sup e - e k) • g k, fun k => ?_⟩
  rw [resF_smul, hg, smul_smul, map_pow, ← pow_add,
    Nat.sub_add_cancel (Finset.le_sup (f := e) (Finset.mem_univ k))]

/- English proof (translation)
Establish `hO : O ≤ stdOpen A n k ⊓ stdOpen A n j` using `le_inf hk hj`. Use `congrArg (resF G hO) (hg k)` as an intermediate fact. Rewrite `this` using `[resF_resF, resF_smul, map_pow, resO_resO, resF_resF]`. Conclude with `this`.
-/
private lemma local_res {G : (projectiveSpace A n).Modules} {j : Fin (n + 1)} {s : Γ(G, stdOpen A n j)}
    {a : ℕ} {g : ∀ k, Γ(G, stdOpen A n k)}
    (hg : ∀ k, resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (g k) =
        resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (yR k j) ^ a •
          resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n j) s)
    (k : Fin (n + 1)) {O : (projectiveSpace A n).Opens} (hk : O ≤ stdOpen A n k)
    (hj : O ≤ stdOpen A n j) :
    resF G hk (g k) = resO hk (yR k j) ^ a • resF G hj s := by
  have hO : O ≤ stdOpen A n k ⊓ stdOpen A n j := le_inf hk hj
  have := congrArg (resF G hO) (hg k)
  rw [resF_resF, resF_smul, map_pow, resO_resO, resF_resF] at this
  exact this

/- English proof (translation)
Establish `key : ∀ k l, ∃ b : ℕ, resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k j) ^ b • (resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (g k) - resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k l) ^ a • resF G (inf_le_r …`. Introduce `k l`. Apply `qcoh_exists_pow_smul_eq_zero G (isAffineOpen_stdOpen_inf k l)` to reduce the goal to its premises. Use `set W := stdOpen A n k ⊓ stdOpen A n l`. Use `set f := resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j)`.

Establish `hO : (projectiveSpace A n).basicOpen f = W ⊓ (stdOpen A n k ⊓ stdOpen A n j)`. Establish `h1 : (projectiveSpace A n).basicOpen f = W ⊓ (projectiveSpace A n).basicOpen (yR (A` using `A) k j) := Scheme.basicOpen_res _ _ _`. Rewrite using `[h1, basicOpen_yR]`. Establish `hOW : (projectiveSpace A n).basicOpen f ≤ W` using `(projectiveSpace A n).basicOpen_le f`. Establish `hOk : (projectiveSpace A n).basicOpen f ≤ stdOpen A n k` using `hOW.trans inf_le_left`.

Establish `hOl : (projectiveSpace A n).basicOpen f ≤ stdOpen A n l` using `hOW.trans inf_le_right`. Establish `hOj : (projectiveSpace A n).basicOpen f ≤ stdOpen A n j` using `hO.le.trans (inf_le_right.trans inf_le_right)`. Rewrite using `[map_sub, resF_resF, resF_smul, resF_resF, map_pow, resO_resO, local_res hg k hOk hOj, local_res hg l hOl hOj, smul_smul, sub_eq_zero]`. Use `congr 1`. Establish `hr0 : resO (inf_le_right : W ≤ stdOpen A n l) (yR (A` using `A) l j) * resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) = resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j) := ProjTwist.ratio_mul_ratio (𝒜 := grading A n) (X_mem k) (X_mem l) (X_mem j)`.

Establish `hr` using `congrArg (resO hOW) hr0`. Rewrite `hr` using `[map_mul, resO_resO, resO_resO, resO_resO]`. Rewrite using `[← hr, mul_pow, mul_comm]`. Use `choose b hb using key`. Use `⟨Finset.univ.sup fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2, fun k l => ?_⟩` and prove the remaining obligations.

Establish `hle : b k l ≤ Finset.univ.sup fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2` using `Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2) (Finset.mem_univ (k, l))`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, mul_smul, hb k l, smul_zero]`.
-/
private lemma exists_kill (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] (j : Fin (n + 1))
    (s : Γ(G, stdOpen A n j)) (a : ℕ) (g : ∀ k, Γ(G, stdOpen A n k))
    (hg : ∀ k, resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (g k) =
        resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n k) (yR k j) ^ a •
          resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n j ≤ stdOpen A n j) s) :
    ∃ b : ℕ, ∀ k l,
      resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k j) ^ b •
        (resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (g k) -
          resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k l) ^ a •
            resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n l) (g l)) = 0 := by
  have key : ∀ k l, ∃ b : ℕ,
      resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k j) ^ b •
        (resF G (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (g k) -
          resO (inf_le_left : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n k) (yR k l) ^ a •
            resF G (inf_le_right : stdOpen A n k ⊓ stdOpen A n l ≤ stdOpen A n l) (g l)) = 0 := by
    intro k l
    apply qcoh_exists_pow_smul_eq_zero G (isAffineOpen_stdOpen_inf k l)
    set W := stdOpen A n k ⊓ stdOpen A n l
    set f := resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j)
    have hO : (projectiveSpace A n).basicOpen f = W ⊓ (stdOpen A n k ⊓ stdOpen A n j) := by
      have h1 : (projectiveSpace A n).basicOpen f =
          W ⊓ (projectiveSpace A n).basicOpen (yR (A := A) k j) :=
        Scheme.basicOpen_res _ _ _
      rw [h1, basicOpen_yR]
    have hOW : (projectiveSpace A n).basicOpen f ≤ W := (projectiveSpace A n).basicOpen_le f
    have hOk : (projectiveSpace A n).basicOpen f ≤ stdOpen A n k := hOW.trans inf_le_left
    have hOl : (projectiveSpace A n).basicOpen f ≤ stdOpen A n l := hOW.trans inf_le_right
    have hOj : (projectiveSpace A n).basicOpen f ≤ stdOpen A n j :=
      hO.le.trans (inf_le_right.trans inf_le_right)
    rw [map_sub, resF_resF, resF_smul, resF_resF, map_pow, resO_resO,
      local_res hg k hOk hOj, local_res hg l hOl hOj, smul_smul, sub_eq_zero]
    congr 1
    have hr0 : resO (inf_le_right : W ≤ stdOpen A n l) (yR (A := A) l j) *
        resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) =
        resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j) :=
      ProjTwist.ratio_mul_ratio (𝒜 := grading A n) (X_mem k) (X_mem l) (X_mem j)
    have hr := congrArg (resO hOW) hr0
    rw [map_mul, resO_resO, resO_resO, resO_resO] at hr
    rw [← hr, mul_pow, mul_comm]
  choose b hb using key
  refine ⟨Finset.univ.sup fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2, fun k l => ?_⟩
  have hle : b k l ≤ Finset.univ.sup fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2 :=
    Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => b p.1 p.2) (Finset.mem_univ (k, l))
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hb k l, smul_zero]

/- English proof (translation)
Take `⟨a, g, hg⟩` from `exists_local_uniform G j s`. Take `⟨b, hb⟩` from `exists_kill G j s a g hg`. Use `⟨a + b, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right a b) hm)`. Establish `hdb : b ≤ d` using `by omega`.

Set `ρ : ∀ k : ULift.{u} (Fin (n + 1)), Γ(twist G (a + d : ℕ), stdOpen A n k.down)` to `fun k => tensorBasisMap G (twistingSheaf (grading A n) (a + d : ℕ)) (upowS k.down (a + d : ℕ)) (le_rfl : stdOpen A n k.down ≤ stdOpen A n k.down) (yR (A := A) k.down j ^ d • g k.down)`. Establish `hcov : ∀ x ∈ (⊤ : (projectiveSpace A n).Opens), ∃ k : ULift.{u} (Fin (n + 1)), x ∈ stdOpen A n k.down`. Introduce `x _`. Establish `hx : x ∈ ⨆ i, stdOpen A n i` using `by rw [iSup_stdOpen]; trivial`. Take `⟨k, hk⟩` from `Opens.mem_iSup.1 hx`.

Conclude with `⟨⟨k⟩, hk⟩`. Establish `hcompat : ∀ k l : ULift.{u} (Fin (n + 1)), resF (twist G (a + d : ℕ)) (inf_le_left : stdOpen A n k.down ⊓ stdOpen A n l.down ≤ stdOpen A n k.down) (ρ k) = resF (twist G (a + d : ℕ)) (inf_le_right : stdOpen A n k.down ⊓ stdOpen A n l.down ≤ stdOpen A n l.down) (ρ l)`. Introduce and unpack `⟨k⟩ ⟨l⟩`. Simplify using `only [ρ]`. Unfold `twist`.

Rewrite using `[tensorBasisMap_res, tensorBasisMap_res, tensorBasisMap_change (s := upowS k (a + d : ℕ)) (upowS l (a + d : ℕ)) (inf_le_left.trans le_rfl) (inf_le_right.trans le_rfl) _ (upowS_res k l (a + d))]`. Use `congr 1`. Use `set W := stdOpen A n k ⊓ stdOpen A n l`. Establish `hr0 : resO (inf_le_right : W ≤ stdOpen A n l) (yR (A` using `A) l j) * resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) = resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j) := ProjTwist.ratio_mul_ratio (𝒜 := grading A n) (X_mem k) (X_mem l) (X_mem j)`. Establish `e1` using `hb k l`.

Establish `e2 : resO (inf_le_left : W ≤ stdOpen A n k) (yR (A` using `A) k j) ^ d • (resF G (inf_le_left : W ≤ stdOpen A n k) (g k) - resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) ^ a • resF G (inf_le_right : W ≤ stdOpen A n l) (g l)) = 0 := by`. Rewrite using `[← Nat.sub_add_cancel hdb, pow_add, mul_smul, e1, smul_zero]`. Rewrite `e2` using `[smul_sub, sub_eq_zero]`. Express the relevant statement in the definitionally equal form `resF G (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j ^ d • g k) = (resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) ^ (a + d)) • resF G (inf_le_right : W ≤ stdOpen A n l) (yR (A := A) l j ^ d • g l)`. Rewrite using `[resF_smul, resF_smul, map_pow, map_pow, e2, smul_smul, smul_smul, ← hr0]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht⟩` from `sheaf_exists_glue ⟨(twist G (a + d : ℕ)).presheaf, (twist G (a + d : ℕ)).isSheaf⟩ (V := ⊤) (fun k : ULift.{u} (Fin (n + 1)) => stdOpen A n k.down) (fun _ => le_top) hcov ρ hcompat`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `htj : resF (twist G (a + d : ℕ)) le_top t = ρ ⟨j⟩` using `ht ⟨j⟩`.

Use `htj.trans ?_` and prove the remaining obligations. Establish `hjj : yR (A` using `A) j j = 1 := ProjTwist.ratio_self (X_mem j)`. Establish `hgj : g j = s`. Apply `resF_injective_of_le G (inf_le_left : stdOpen A n j ⊓ stdOpen A n j ≤ stdOpen A n j) (le_inf le_rfl le_rfl)` to reduce the goal to its premises. Rewrite using `[hg j, hjj, map_one, one_pow, one_smul]`.

Establish `hx : yR (A` using `A) j j ^ d • g j = s := by rw [hjj, one_pow, one_smul, hgj]`. Conclude with `congrArg (tensorBasisMap G (twistingSheaf (grading A n) (a + d : ℕ)) (upowS j (a + d : ℕ)) (le_rfl : stdOpen A n j ≤ stdOpen A n j)) hx`.
-/
theorem exists_extend (G : (projectiveSpace A n).Modules) [G.IsQuasicoherent] (j : Fin (n + 1))
    (s : Γ(G, stdOpen A n j)) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ t : Γ(twist G m, ⊤),
      resF (twist G m) le_top t =
        tensorBasisMap G (twistingSheaf (grading A n) m) (ProjTwist.upow (grading A n) (X_mem j) m)
          le_rfl s := by
  obtain ⟨a, g, hg⟩ := exists_local_uniform G j s
  obtain ⟨b, hb⟩ := exists_kill G j s a g hg
  refine ⟨a + b, fun m hm => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (le_trans (Nat.le_add_right a b) hm)
  have hdb : b ≤ d := by omega

  let ρ : ∀ k : ULift.{u} (Fin (n + 1)), Γ(twist G (a + d : ℕ), stdOpen A n k.down) := fun k =>
    tensorBasisMap G (twistingSheaf (grading A n) (a + d : ℕ))
      (upowS k.down (a + d : ℕ))
      (le_rfl : stdOpen A n k.down ≤ stdOpen A n k.down) (yR (A := A) k.down j ^ d • g k.down)
  have hcov : ∀ x ∈ (⊤ : (projectiveSpace A n).Opens),
      ∃ k : ULift.{u} (Fin (n + 1)), x ∈ stdOpen A n k.down := by
    intro x _
    have hx : x ∈ ⨆ i, stdOpen A n i := by rw [iSup_stdOpen]; trivial
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hx
    exact ⟨⟨k⟩, hk⟩
  have hcompat : ∀ k l : ULift.{u} (Fin (n + 1)),
      resF (twist G (a + d : ℕ))
          (inf_le_left : stdOpen A n k.down ⊓ stdOpen A n l.down ≤ stdOpen A n k.down) (ρ k) =
        resF (twist G (a + d : ℕ))
          (inf_le_right : stdOpen A n k.down ⊓ stdOpen A n l.down ≤ stdOpen A n l.down) (ρ l) := by
    rintro ⟨k⟩ ⟨l⟩
    simp only [ρ]
    unfold twist
    rw [tensorBasisMap_res, tensorBasisMap_res,
      tensorBasisMap_change (s := upowS k (a + d : ℕ))
        (upowS l (a + d : ℕ)) (inf_le_left.trans le_rfl)
        (inf_le_right.trans le_rfl) _ (upowS_res k l (a + d))]
    congr 1
    set W := stdOpen A n k ⊓ stdOpen A n l
    have hr0 : resO (inf_le_right : W ≤ stdOpen A n l) (yR (A := A) l j) *
        resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) =
        resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j) :=
      ProjTwist.ratio_mul_ratio (𝒜 := grading A n) (X_mem k) (X_mem l) (X_mem j)
    have e1 := hb k l
    have e2 : resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j) ^ d •
        (resF G (inf_le_left : W ≤ stdOpen A n k) (g k) -
          resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) ^ a •
            resF G (inf_le_right : W ≤ stdOpen A n l) (g l)) = 0 := by
      rw [← Nat.sub_add_cancel hdb, pow_add, mul_smul, e1, smul_zero]
    rw [smul_sub, sub_eq_zero] at e2
    change resF G (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k j ^ d • g k) =
      (resO (inf_le_left : W ≤ stdOpen A n k) (yR (A := A) k l) ^ (a + d)) •
        resF G (inf_le_right : W ≤ stdOpen A n l) (yR (A := A) l j ^ d • g l)
    rw [resF_smul, resF_smul, map_pow, map_pow, e2, smul_smul, smul_smul, ← hr0]
    congr 1
    ring
  obtain ⟨t, ht⟩ := sheaf_exists_glue ⟨(twist G (a + d : ℕ)).presheaf, (twist G (a + d : ℕ)).isSheaf⟩
    (V := ⊤) (fun k : ULift.{u} (Fin (n + 1)) => stdOpen A n k.down) (fun _ => le_top) hcov ρ
    hcompat
  refine ⟨t, ?_⟩
  have htj : resF (twist G (a + d : ℕ)) le_top t = ρ ⟨j⟩ := ht ⟨j⟩
  refine htj.trans ?_
  have hjj : yR (A := A) j j = 1 := ProjTwist.ratio_self (X_mem j)
  have hgj : g j = s := by
    apply resF_injective_of_le G (inf_le_left : stdOpen A n j ⊓ stdOpen A n j ≤ stdOpen A n j)
      (le_inf le_rfl le_rfl)
    rw [hg j, hjj, map_one, one_pow, one_smul]
  have hx : yR (A := A) j j ^ d • g j = s := by rw [hjj, one_pow, one_smul, hgj]
  exact congrArg (tensorBasisMap G (twistingSheaf (grading A n) (a + d : ℕ))
    (upowS j (a + d : ℕ)) (le_rfl : stdOpen A n j ≤ stdOpen A n j)) hx

def twistLinear (G : (projectiveSpace A n).Modules) (j : Fin (n + 1)) (q : ℤ) :
    Γ(G, stdOpen A n j) →ₗ[Γ(projectiveSpace A n, stdOpen A n j)] Γ(twist G q, stdOpen A n j) where
  toFun := tensorBasisMap G (twistingSheaf (grading A n) q) (upowS j q)
    (le_rfl : stdOpen A n j ≤ stdOpen A n j)
  map_add' := map_add _
  map_smul' r m := tensorBasisMap_smul _ r m

/- English proof (translation)
The claim follows from `(tensorBasisMap_bijective (ProjTwist.isBasisOn_upow (grading A n) (X_mem j) q) le_rfl).2`.
-/
lemma twistLinear_surjective (G : (projectiveSpace A n).Modules) (j : Fin (n + 1)) (q : ℤ) :
    Function.Surjective (twistLinear G j q) :=
  (tensorBasisMap_bijective (ProjTwist.isBasisOn_upow (grading A n) (X_mem j) q) le_rfl).2

/- English proof (translation)
Take `⟨hqc, hfin⟩` from `hG`. Establish `hfg : ∀ j : Fin (n + 1), ∃ S : Finset Γ(G, stdOpen A n j), Submodule.span Γ(projectiveSpace A n, stdOpen A n j) (S : Set Γ(G, stdOpen A n j)) = ⊤` using `fun j => (hfin _ (isAffineOpen_stdOpen j)).fg_top`. Use `choose S hS using hfg`. Establish `hext : ∀ p : (j : Fin (n + 1)) × S j, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∃ t : Γ(twist G m, ⊤), resF (twist G m) (le_top : stdOpen A n p.1 ≤ ⊤) t = twistLinear G p.1 m p.2.1` using `fun p => exists_extend G p.1 p.2.1`. Use `choose m₀ hm₀ using hext`.

Use `⟨Finset.univ.sup m₀, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hq' : ∀ p, m₀ p ≤ q` using `fun p => (Finset.le_sup (f := m₀) (Finset.mem_univ p)).trans hq`. Use `choose t ht using fun p => hm₀ p q (hq' p)`. Establish `hcov : (⨆ i : ULift.{u} (Fin (n + 1)), stdOpen A n i.down) = ⊤`. Use `le_antisymm le_top ?_` and prove the remaining obligations.

Rewrite using `[← iSup_stdOpen (A := A) (n := n)]`. Conclude with `iSup_le fun j => le_iSup_of_le (⟨j⟩ : ULift.{u} (Fin (n + 1))) le_rfl`. Use `exists_generatingSections (twist G q) (fun i : ULift.{u} (Fin (n + 1)) => stdOpen A n i.down) (fun i => isAffineOpen_stdOpen _) hcov t fun ⟨j⟩ => ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`.

Take `⟨w, rfl⟩` from `twistLinear_surjective G j q z`. Establish `hw : w ∈ Submodule.span Γ(projectiveSpace A n, stdOpen A n j) (S j : Set Γ(G, stdOpen A n j))` using `(hS j).symm ▸ Submodule.mem_top`. Establish `hmap` using `Submodule.mem_map_of_mem (f := twistLinear G j q) hw`. Rewrite `hmap` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ hmap` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨⟨j, ⟨x, hx⟩⟩, ht ⟨j, ⟨x, hx⟩⟩⟩`.
-/
theorem exists_generatingSections_twist (G : (projectiveSpace A n).Modules) (hG : IsCoherent G) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ σ : (twist G q).GeneratingSections, σ.IsFiniteType := by
  obtain ⟨hqc, hfin⟩ := hG
  have hfg : ∀ j : Fin (n + 1), ∃ S : Finset Γ(G, stdOpen A n j),
      Submodule.span Γ(projectiveSpace A n, stdOpen A n j) (S : Set Γ(G, stdOpen A n j)) = ⊤ :=
    fun j => (hfin _ (isAffineOpen_stdOpen j)).fg_top
  choose S hS using hfg
  have hext : ∀ p : (j : Fin (n + 1)) × S j, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∃ t : Γ(twist G m, ⊤), resF (twist G m) (le_top : stdOpen A n p.1 ≤ ⊤) t =
        twistLinear G p.1 m p.2.1 := fun p => exists_extend G p.1 p.2.1
  choose m₀ hm₀ using hext
  refine ⟨Finset.univ.sup m₀, fun q hq => ?_⟩
  have hq' : ∀ p, m₀ p ≤ q := fun p => (Finset.le_sup (f := m₀) (Finset.mem_univ p)).trans hq
  choose t ht using fun p => hm₀ p q (hq' p)
  have hcov : (⨆ i : ULift.{u} (Fin (n + 1)), stdOpen A n i.down) = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← iSup_stdOpen (A := A) (n := n)]
    exact iSup_le fun j => le_iSup_of_le (⟨j⟩ : ULift.{u} (Fin (n + 1))) le_rfl
  refine exists_generatingSections (twist G q) (fun i : ULift.{u} (Fin (n + 1)) => stdOpen A n i.down)
    (fun i => isAffineOpen_stdOpen _) hcov t fun ⟨j⟩ => ?_
  rw [eq_top_iff]
  rintro z -
  obtain ⟨w, rfl⟩ := twistLinear_surjective G j q z
  have hw : w ∈ Submodule.span Γ(projectiveSpace A n, stdOpen A n j) (S j : Set Γ(G, stdOpen A n j)) :=
    (hS j).symm ▸ Submodule.mem_top
  have hmap := Submodule.mem_map_of_mem (f := twistLinear G j q) hw
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨⟨j, ⟨x, hx⟩⟩, ht ⟨j, ⟨x, hx⟩⟩⟩

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
