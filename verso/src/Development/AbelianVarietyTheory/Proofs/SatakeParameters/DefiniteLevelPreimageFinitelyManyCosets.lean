import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongruenceLevelContained
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LevCosetFin

open ReciprocityTheory.Aut

section Grp

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Establish `e : (d : AL L) = algebraMap L (AL L) (d : L)` using `(map_natCast _ d).symm`. Rewrite using `[e]`. Conclude with `(IsUnit.mk0 (d : L) (Nat.cast_ne_zero.2 hd.ne')).map _`.
-/
theorem natCast_isUnit_AL {d : ℕ} (hd : 0 < d) : IsUnit (d : AL L) := by
  have e : (d : AL L) = algebraMap L (AL L) (d : L) := (map_natCast _ d).symm
  rw [e]
  exact (IsUnit.mk0 (d : L) (Nat.cast_ne_zero.2 hd.ne')).map _

/- English proof (translation)
Take `⟨Q, hQ, c, hc⟩` from `GlobalTheory.IsotOrth.exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L) (d * d) (Nat.mul_pos hd hd)`. Use `haveI := hQ`. Set `cls : GAf L n → Fin n → Fin n → Q` to `fun κ i j => if h : (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L then c ⟨_, h⟩ else c 0`. Establish `key : ∀ a ∈ S, ∀ b ∈ S, cls a = cls b → a⁻¹ * b ∈ Umax L n`. Introduce `a ha b hb hab`.

Establish `hdiff : ∀ k l, ∃ y ∈ ALint L, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l - (a.1 : Matrix (Fin n) (Fin n) (AL L)) k l = (d : AL L) * y`. Introduce `k l`. Establish `e` using `congrFun (congrFun hab k) l`. Simplify using `only [cls, dif_pos (hS a ha k l).1, dif_pos (hS b hb k l).1] at e`. Take `⟨z, hz⟩` from `hc _ _ e.symm`.

Use `⟨z.1, z.2, ?_⟩` and prove the remaining obligations. Establish `hz'` using `congrArg Subtype.val hz`. Apply `(natCast_isUnit_AL (L := L) hd).mul_left_cancel` to reduce the goal to its premises. Move the coercions through the operations in `at hz'`. Rewrite using `[mul_sub, hz', mul_assoc]`.

Use `choose y hy hye using hdiff`. Establish `h0 : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1`. Establish `: (((a⁻¹ * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1` using `by simp`. Simplify using `using this`. Establish `h1 : (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 + ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - (a.1 : Matrix (Fin n) (Fin n) (AL L)))`.

Rewrite using `[Matrix.mul_sub, h0, add_sub_cancel]`. Both sides reduce to the same expression. Introduce `i j`. Use `show (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L`. Rewrite using `[h1, Matrix.add_apply, Matrix.mul_apply]`.

Use `add_mem ?_ (Subring.sum_mem _ fun k _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.one_apply] split_ifs exacts [one_mem _, zero_mem _]`. Rewrite using `[Matrix.sub_apply, hye k j, ← mul_assoc, mul_comm _ (d : AL L)]`. Conclude with `mul_mem (hS a ha i k).2 (hy k j)`. Set `T : Set (Fin n → Fin n → Q)` to `cls '' S`.

Establish `hT : T.Finite` using `Set.toFinite T`. Set `rep : (Fin n → Fin n → Q) → GAf L n` to `fun t => if h : t ∈ T then h.choose else 1`. Use `⟨hT.toFinset.image rep, fun κ hκ => ?_⟩` and prove the remaining obligations. Establish `ht : cls κ ∈ T` using `⟨κ, hκ, rfl⟩`. Establish `hr : rep (cls κ) = ht.choose` using `dif_pos ht`.

Use `⟨rep (cls κ), Finset.mem_image.2 ⟨cls κ, hT.mem_toFinset.2 ht, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Conclude with `key _ ht.choose_spec.1 _ hκ ht.choose_spec.2`.
-/
theorem exists_finset_of_bdd (d : ℕ) (hd : 0 < d) (S : Set (GAf L n))
    (hS : ∀ κ ∈ S, ∀ i j, (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L ∧
        (d : AL L) * ((κ⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L) :
    ∃ F : Finset (GAf L n), ∀ κ ∈ S, ∃ f ∈ F, f⁻¹ * κ ∈ Umax L n := by
  classical
  obtain ⟨Q, hQ, c, hc⟩ := GlobalTheory.IsotOrth.exists_finite_class (F := NumberField.maximalRealSubfield L) (E := L)
    (d * d) (Nat.mul_pos hd hd)
  haveI := hQ
  let cls : GAf L n → Fin n → Fin n → Q := fun κ i j =>
    if h : (d : AL L) * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L then c ⟨_, h⟩ else c 0
  have key : ∀ a ∈ S, ∀ b ∈ S, cls a = cls b → a⁻¹ * b ∈ Umax L n := by
    intro a ha b hb hab
    have hdiff : ∀ k l, ∃ y ∈ ALint L, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l -
        (a.1 : Matrix (Fin n) (Fin n) (AL L)) k l = (d : AL L) * y := by
      intro k l
      have e := congrFun (congrFun hab k) l
      simp only [cls, dif_pos (hS a ha k l).1, dif_pos (hS b hb k l).1] at e
      obtain ⟨z, hz⟩ := hc _ _ e.symm
      refine ⟨z.1, z.2, ?_⟩
      have hz' := congrArg Subtype.val hz
      apply (natCast_isUnit_AL (L := L) hd).mul_left_cancel
      push_cast at hz'
      rw [mul_sub, hz', mul_assoc]
    choose y hy hye using hdiff
    have h0 : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      have : (((a⁻¹ * a).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
      simpa using this
    have h1 : (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 +
        ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) *
          ((b.1 : Matrix (Fin n) (Fin n) (AL L)) - (a.1 : Matrix (Fin n) (Fin n) (AL L))) := by
      rw [Matrix.mul_sub, h0, add_sub_cancel]
      rfl
    intro i j
    show (((a⁻¹ * b).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
    rw [h1, Matrix.add_apply, Matrix.mul_apply]
    refine add_mem ?_ (Subring.sum_mem _ fun k _ => ?_)
    · rw [Matrix.one_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    · rw [Matrix.sub_apply, hye k j, ← mul_assoc, mul_comm _ (d : AL L)]
      exact mul_mem (hS a ha i k).2 (hy k j)
  let T : Set (Fin n → Fin n → Q) := cls '' S
  have hT : T.Finite := Set.toFinite T
  let rep : (Fin n → Fin n → Q) → GAf L n := fun t => if h : t ∈ T then h.choose else 1
  refine ⟨hT.toFinset.image rep, fun κ hκ => ?_⟩
  have ht : cls κ ∈ T := ⟨κ, hκ, rfl⟩
  have hr : rep (cls κ) = ht.choose := dif_pos ht
  refine ⟨rep (cls κ), Finset.mem_image.2 ⟨cls κ, hT.mem_toFinset.2 ht, rfl⟩, ?_⟩
  rw [hr]
  exact key _ ht.choose_spec.1 _ hκ ht.choose_spec.2

end Grp

end GlobalTheory.LevCosetFin

namespace GlobalTheory.LevCosetFin

section Den

variable {D : D7}

/- English proof (translation)
Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem z hz`. Apply `Subring.subset_closure` to reduce the goal to its premises. Break down `hz with ⟨⟨s, t, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩` into its components or cases. Use `right`.

Conclude with `⟨t, by simp⟩`. Use `left`. Conclude with `⟨a, ha, by simp⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`.

Consider the case `one => rw [map_one]`. Conclude with `one_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `neg x _ hx => rw [map_neg]`.

Conclude with `neg_mem hx`. Consider the case `mul x y _ _ hx hy => rw [map_mul]`. Conclude with `mul_mem hx hy`.
-/
theorem comm_mem_intT {x : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F}
    (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)) x ∈ GlobalTheory.LatCongImage.intT D.host.F := by
  induction hx using Subring.closure_induction with
  | mem z hz =>
    apply Subring.subset_closure
    rcases hz with ⟨⟨s, t, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · right
      exact ⟨t, by simp⟩
    · left
      exact ⟨a, ha, by simp⟩
  | zero => rw [map_zero]; exact zero_mem _
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end Den

end GlobalTheory.LevCosetFin

namespace GlobalTheory.LevCosetFin

section Den2

variable {D : D7}

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨⟨B, B', hBB', hB'B, hmat⟩, -⟩` from `hP`. Set `cmr : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E` to `(Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toAlgHom.toRingHom`. Set `βs` to `(β.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr`. Set `βi` to `((β⁻¹).1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr`. Take `⟨d, hd, hdm⟩` from `GlobalTheory.LatCongImage.exists_nat_mul_mem_family D.host.F (fun p : ((Fin V.rank × Fin n) ⊕ (Fin n × Fin V.rank)) ⊕ ((Fin V.rank × Fin V.rank) ⊕ (Fin V.rank × Fin V.rank)) => Sum.elim (Sum.elim (fun q => B q.1 q.2) (fun q => B' q.1 q.2)) (Sum.elim (fun q => βs q.1 q.2) (fun q = …`.

Use `⟨d ^ 4, by positivity, fun κ hκ i j => ?_⟩` and prove the remaining obligations. Establish `h1 : Formalism.IndefR.Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Formalism.IndefR.Lev.flag1L Ld)` using `hκ`. Take `⟨y, hy⟩` from `Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev h1)`. Establish `hM1` using `congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => (g.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) hy`. Use `set Mf := (finHom V (P.ψ κ)).1 with hMf`.

Establish `hM2 : β.1 * ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val) * (β⁻¹).1 = Mf.map (Formalism.IndefR.Lev.swapAE D)` using `hM1`. Set `Ym` to `((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val).map cmr`. Establish `hback : (Mf.map (Formalism.IndefR.Lev.swapAE D)).map cmr = Mf`. Use extensionality with `a b`. Use `show (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)) ((Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E) (Mf a b)) = Mf a b`.

Rewrite using `[← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]`. Establish `hM3 : Mf = βs * Ym * βi`. Rewrite using `[← hback, ← hM2, Matrix.map_mul, Matrix.map_mul]`. Use `set K := (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hK`. Establish `hK2 : K = B' * Mf * B`.

Establish `e` using `hmat κ`. Establish `e' : Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ) = Mf` using `rfl`. Rewrite `e` using `[e']`. Rewrite using `[e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB'B, Matrix.one_mul, Matrix.mul_assoc, hB'B, Matrix.mul_one]`. Establish `hκij : (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j = Formalism.IndefR.principalLevelFrame.tensCastR hF (K i j)`.

Rewrite using `[hK, Matrix.map_apply, RingEquiv.apply_symm_apply]`. Set `Bs' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)` to `(d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B'`. Set `Bs : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)` to `(d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B`. Set `βs' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)` to `(d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βs`. Set `βi' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)` to `(d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βi`.

Set `Ms : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)` to `βs' * Ym * βi'`. Establish `hB'1 : ∀ a b, Bs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F` using `fun a b => by show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B' a b ∈ _; exact hdm (Sum.inl (Sum.inr (a, b)))`. Establish `hB1 : ∀ a b, Bs a b ∈ GlobalTheory.LatCongImage.intT D.host.F` using `fun a b => by show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B a b ∈ _; exact hdm (Sum.inl (Sum.inl (a, b)))`. Establish `hβs1 : ∀ a b, βs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F` using `fun a b => by show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βs a b ∈ _; exact hdm (Sum.inr (Sum.inl (a, b)))`. Establish `hβi1 : ∀ a b, βi' a b ∈ GlobalTheory.LatCongImage.intT D.host.F` using `fun a b => by show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βi a b ∈ _; exact hdm (Sum.inr (Sum.inr (a, b)))`.

Establish `hY1 : ∀ a b, Ym a b ∈ GlobalTheory.LatCongImage.intT D.host.F` using `fun a b => comm_mem_intT (D := D) ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b).2`. Establish `hMs : ∀ a b, Ms a b ∈ GlobalTheory.LatCongImage.intT D.host.F` using `GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hβs1 hY1) hβi1`. Establish `hint : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * K i j ∈ GlobalTheory.LatCongImage.intT D.host.F`. Establish `hK3 : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • K = Bs' * Ms * Bs`. Rewrite using `[hK2, hM3]`.

Simplify using `only [Bs', Bs, Ms, βs', βi', Matrix.mul_smul, Matrix.smul_mul, smul_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e` using `congrFun (congrFun hK3 i) j`.

Rewrite `e` using `[Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[e]`. Conclude with `GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hB'1 hMs) hB1 i j`. Rewrite using `[hκij, ← map_natCast (Formalism.IndefR.principalLevelFrame.tensCastR hF) (d ^ 4), ← map_mul]`. Conclude with `GlobalTheory.LatCongImage.swap_mem D.host.F hF hint`.
-/
theorem exists_den (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (P : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (hF : D.host.F = maximalRealSubfield D.host.E) (hP : Formalism.IndefR.principalLevelFrame.StdPsi hF P)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Ld : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∃ d : ℕ, 0 < d ∧ ∀ κ, (finHom V).rangeRestrict (P.ψ κ) ∈ (levEnv V β Ld).J → ∀ i j,
      (d : AL D.host.E) * (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j ∈ ALint D.host.E := by
  obtain ⟨⟨B, B', hBB', hB'B, hmat⟩, -⟩ := hP
  let cmr : D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F →+* FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F)).toAlgHom.toRingHom
  let βs := (β.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr
  let βi := ((β⁻¹).1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D)).map cmr
  obtain ⟨d, hd, hdm⟩ := GlobalTheory.LatCongImage.exists_nat_mul_mem_family D.host.F
    (fun p : ((Fin V.rank × Fin n) ⊕ (Fin n × Fin V.rank)) ⊕ ((Fin V.rank × Fin V.rank) ⊕ (Fin V.rank × Fin V.rank)) =>
      Sum.elim (Sum.elim (fun q => B q.1 q.2) (fun q => B' q.1 q.2))
        (Sum.elim (fun q => βs q.1 q.2) (fun q => βi q.1 q.2)) p)
  refine ⟨d ^ 4, by positivity, fun κ hκ i j => ?_⟩
  have h1 : Formalism.IndefR.Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Formalism.IndefR.Lev.flag1L Ld) := hκ
  obtain ⟨y, hy⟩ := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev h1)
  have hM1 := congrArg (fun g : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) => (g.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.IndefR.Lev.EAf D))) hy
  set Mf := (finHom V (P.ψ κ)).1 with hMf
  have hM2 : β.1 * ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val) *
      (β⁻¹).1 = Mf.map (Formalism.IndefR.Lev.swapAE D) := hM1
  let Ym := ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)).map Subtype.val).map cmr
  have hback : (Mf.map (Formalism.IndefR.Lev.swapAE D)).map cmr = Mf := by
    ext a b
    show (Algebra.TensorProduct.comm D.host.F D.host.E (Formalism.L2.Herm.Af D.host.F))
      ((Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E) (Mf a b)) = Mf a b
    rw [← Algebra.TensorProduct.comm_symm, AlgEquiv.symm_apply_apply]
  have hM3 : Mf = βs * Ym * βi := by
    rw [← hback, ← hM2, Matrix.map_mul, Matrix.map_mul]
  set K := (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hK
  have hK2 : K = B' * Mf * B := by
    have e := hmat κ
    have e' : Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (P.ψ κ) = Mf := rfl
    rw [e'] at e
    rw [e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB'B, Matrix.one_mul, Matrix.mul_assoc, hB'B, Matrix.mul_one]
  have hκij : (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)) i j = Formalism.IndefR.principalLevelFrame.tensCastR hF (K i j) := by
    rw [hK, Matrix.map_apply, RingEquiv.apply_symm_apply]
  let Bs' : Matrix (Fin n) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B'
  let Bs : Matrix (Fin V.rank) (Fin n) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • B
  let βs' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βs
  let βi' : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • βi
  let Ms : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := βs' * Ym * βi'
  have hB'1 : ∀ a b, Bs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B' a b ∈ _; exact hdm (Sum.inl (Sum.inr (a, b)))
  have hB1 : ∀ a b, Bs a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * B a b ∈ _; exact hdm (Sum.inl (Sum.inl (a, b)))
  have hβs1 : ∀ a b, βs' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βs a b ∈ _; exact hdm (Sum.inr (Sum.inl (a, b)))
  have hβi1 : ∀ a b, βi' a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b => by
    show (d : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * βi a b ∈ _; exact hdm (Sum.inr (Sum.inr (a, b)))
  have hY1 : ∀ a b, Ym a b ∈ GlobalTheory.LatCongImage.intT D.host.F := fun a b =>
    comm_mem_intT (D := D) ((y.1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b).2
  have hMs : ∀ a b, Ms a b ∈ GlobalTheory.LatCongImage.intT D.host.F :=
    GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hβs1 hY1) hβi1
  have hint : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) * K i j ∈ GlobalTheory.LatCongImage.intT D.host.F := by
    have hK3 : ((d ^ 4 : ℕ) : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) • K = Bs' * Ms * Bs := by
      rw [hK2, hM3]
      simp only [Bs', Bs, Ms, βs', βi', Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      congr 1
      push_cast
      ring
    have e := congrFun (congrFun hK3 i) j
    rw [Matrix.smul_apply, smul_eq_mul] at e
    rw [e]
    exact GlobalTheory.LatCongImage.mul_apply_mem _ _ _ (GlobalTheory.LatCongImage.mul_apply_mem _ _ _ hB'1 hMs) hB1 i j
  rw [hκij, ← map_natCast (Formalism.IndefR.principalLevelFrame.tensCastR hF) (d ^ 4), ← map_mul]
  exact GlobalTheory.LatCongImage.swap_mem D.host.F hF hint

end Den2

end GlobalTheory.LevCosetFin

open GlobalTheory.LevCosetFin in

/- English proof (translation)
Introduce `D cf nch tp X M rep hA j t`. Take `⟨d, hd, hden⟩` from `exists_den (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) (X.R.βV j) (X.R.datVt j t)`. Take `⟨F, hF⟩` from `exists_finset_of_bdd d hd {κ | (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J} (fun κ hκ a b => ⟨hden κ hκ a b, hden κ⁻¹ (by show (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ⁻¹) ∈ _`. Rewrite using `[map_inv, map_inv]`. Conclude with `inv_mem hκ) a b⟩)`.

Conclude with `⟨F, fun κ hκ => hF κ hκ⟩`.
-/
theorem GlobalTheory.LevCosetFin.preimage_levEnv_finite_cosets : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ F : Finset (GAf D.host.E D.R.nV), ∀ κ, (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J → ∃ f ∈ F, f⁻¹ * κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := by
  intro D cf nch tp X M rep hA j t
  obtain ⟨d, hd, hden⟩ := exists_den (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) (X.R.βV j) (X.R.datVt j t)
  obtain ⟨F, hF⟩ := exists_finset_of_bdd d hd
    {κ | (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J}
    (fun κ hκ a b => ⟨hden κ hκ a b, hden κ⁻¹ (by
      show (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ⁻¹) ∈ _
      rw [map_inv, map_inv]
      exact inv_mem hκ) a b⟩)
  exact ⟨F, fun κ hκ => hF κ hκ⟩
