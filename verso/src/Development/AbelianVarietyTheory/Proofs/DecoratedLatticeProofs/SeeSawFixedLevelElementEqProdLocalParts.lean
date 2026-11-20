import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelCut

variable {D : D7}

/- English proof (translation)
Establish `key : ∀ z : (A × B) ⊗[F] E, z = (LinearMap.inl F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) + (LinearMap.inr F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z)`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [← TensorProduct.add_tmul]`.

Consider the case `add x y hx hy`. Simplify using `only [map_add]`. Rewrite using `[add_add_add_comm, ← hx, ← hy]`. Rewrite using `[key z, h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem tensor_prod_zero {F A B E : Type} [Field F] [CommRing A] [CommRing B] [CommRing E] [Algebra F A]
    [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z = 0)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z = 0) : z = 0 := by
  have key : ∀ z : (A × B) ⊗[F] E, z =
      (LinearMap.inl F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      (LinearMap.inr F A B).rTensor E (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [key z, h1, h2]; simp

/- English proof (translation)
The claim follows from `tensor_prod_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) (E := D.host.E) z h1 h2`.
-/
theorem adele_zero (z : AE D) (h1 : infPart D z = 0) (h2 : finPart D z = 0) : z = 0 :=
  tensor_prod_zero (F := D.host.F) (A := Ainf D.host.F) (B := Af D.host.F) (E := D.host.E) z h1 h2

/- English proof (translation)
Use `show infHom V y = 1`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(mt V y).map (infPart D) = 1`. Use extensionality with `i j`. Use `hy i j` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, RingHom.map_sub, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.
-/
theorem mem_GfC_of (V : HSp D) (y : GA D V) (hy : ∀ i j, infPart D ((mt V y - 1) i j) = 0) : y ∈ GfC V := by
  show infHom V y = 1
  apply Units.ext
  change (mt V y).map (infPart D) = 1
  ext i j
  have := hy i j
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Establish `k1 : (mt V y).map (infPart D) = 1`. Use `congrArg Units.val (show infHom V y = 1 from h1)` as an intermediate fact. Conclude with `this`. Establish `k2 : (mt V y).map (finPart D) = 1`. Use `congrArg Units.val (show finHom V y = 1 from h2)` as an intermediate fact.

Conclude with `this`. Apply `GlobalTheory.SplitCut.mt_injective` to reduce the goal to its premises. Rewrite using `[GlobalTheory.SplitCut.mt_one]`. Use extensionality with `i j`. Apply `sub_eq_zero.mp` to reduce the goal to its premises.

Apply `adele_zero` to reduce the goal to its premises. Rewrite using `[RingHom.map_sub, sub_eq_zero]`. Conclude with `congrFun (congrFun (k1.trans (Matrix.map_one (infPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j`. Rewrite using `[RingHom.map_sub, sub_eq_zero]`. Conclude with `congrFun (congrFun (k2.trans (Matrix.map_one (finPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j`.
-/
theorem eq_one_of_parts (V : HSp D) (y : GA D V) (h1 : y ∈ GfC V) (h2 : y ∈ GinfC V) : y = 1 := by
  have k1 : (mt V y).map (infPart D) = 1 := by
    have := congrArg Units.val (show infHom V y = 1 from h1)
    exact this
  have k2 : (mt V y).map (finPart D) = 1 := by
    have := congrArg Units.val (show finHom V y = 1 from h2)
    exact this
  apply GlobalTheory.SplitCut.mt_injective
  rw [GlobalTheory.SplitCut.mt_one]
  ext i j
  apply sub_eq_zero.mp
  apply adele_zero
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k1.trans (Matrix.map_one (infPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (k2.trans (Matrix.map_one (finPart D) (RingHom.map_zero _) (RingHom.map_one _)).symm) i) j

/- English proof (translation)
Use `mem_GfC_of V x fun i j => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun y : GL (Fin V.rank) (AE D ⧸ idAt D P) => y.1 i j) (show _ = (1 : GL _ _) from hx)`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (idAt D P) (mt V x i j) = _ at h`. Establish `h2 : Ideal.Quotient.mk (idAt D P) (mt V x i j) = Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)`. Apply the tactic sequence `rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.

Establish `h4 : (mt V x - 1) i j ∈ idAt D P`. Rewrite using `[Matrix.sub_apply]`. Conclude with `Ideal.Quotient.eq.mp h2`. Conclude with `(RingHom.mem_ker).mp (Ideal.mem_inf.mp h4).1`.
-/
theorem mem_GfC_of_grpAt (V : HSp D) (P : Pl D → Prop) (x : GA D V) (hx : x ∈ grpAt V P) : x ∈ GfC V := by
  refine mem_GfC_of V x fun i j => ?_
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ idAt D P) => y.1 i j) (show _ = (1 : GL _ _) from hx)
  change Ideal.Quotient.mk (idAt D P) (mt V x i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V x i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have h4 : (mt V x - 1) i j ∈ idAt D P := by
    rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2
  exact (RingHom.mem_ker).mp (Ideal.mem_inf.mp h4).1

/- English proof (translation)
Take `⟨ε, ⟨α, rfl, -⟩, hε⟩` from `he`. Establish `h0 : infPart D (e + cA D e) = 0`. Rewrite using `[hε]`. Conclude with `TensorProduct.zero_tmul _ _`. Use `mem_GfC_of V y fun i j => ?_` and prove the remaining obligations.

Rewrite using `[← hy i j, RingHom.map_mul, h0, zero_mul]`.
-/
theorem mem_GfC_of_supp (V : HSp D) {w : Pl D} (e : AE D) (he : ∃ ε, IsPlaceIdem D w ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε)
    (y : GA D V) (hy : SuppAt e V y) : y ∈ GfC V := by
  obtain ⟨ε, ⟨α, rfl, -⟩, hε⟩ := he
  have h0 : infPart D (e + cA D e) = 0 := by
    rw [hε]
    exact TensorProduct.zero_tmul _ _
  refine mem_GfC_of V y fun i j => ?_
  rw [← hy i j, RingHom.map_mul, h0, zero_mul]

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

variable {D : D7}

/- English proof (translation)
Establish `h` using `congrArg (fun y : GL (Fin V.rank) (AE D ⧸ I) => y.1 i j) (show _ = (1 : GL _ _) from hg)`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (mt V g i j) = _ at h`. Establish `h2 : Ideal.Quotient.mk I (mt V g i j) = Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)`. Apply the tactic sequence `rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Rewrite using `[Matrix.sub_apply]`.

Conclude with `Ideal.Quotient.eq.mp h2`.
-/
theorem entry_mem_of (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : g ∈ congGrp V I) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ I := by
  have h := congrArg (fun y : GL (Fin V.rank) (AE D ⧸ I) => y.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk I (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

/- English proof (translation)
Use `show (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)) (matHom V g) = 1`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I (mt V g i j) = (1 : GL (Fin V.rank) (AE D ⧸ I)).1 i j`. Rewrite using `[Units.val_one]`.

Establish `h2 : Ideal.Quotient.mk I (mt V g i j) = Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)` using `Ideal.Quotient.eq.mpr (by rw [← Matrix.sub_apply]; exact hg i j)`. Apply the tactic sequence `rw [h2]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.
-/
theorem mem_of_entry (V : HSp D) (I : Ideal (AE D)) (g : GA D V) (hg : ∀ i j, (mt V g - 1) i j ∈ I) :
    g ∈ congGrp V I := by
  show (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)) (matHom V g) = 1
  apply Units.ext
  ext i j
  change Ideal.Quotient.mk I (mt V g i j) = (1 : GL (Fin V.rank) (AE D ⧸ I)).1 i j
  rw [Units.val_one]
  have h2 : Ideal.Quotient.mk I (mt V g i j) =
      Ideal.Quotient.mk I ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) :=
    Ideal.Quotient.eq.mpr (by rw [← Matrix.sub_apply]; exact hg i j)
  rw [h2]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Introduce `g hg` and use `mem_of_entry V J g fun i j => h (entry_mem_of V I g hg i j)`.
-/
theorem congGrp_le (V : HSp D) {I J : Ideal (AE D)} (h : I ≤ J) : congGrp V I ≤ congGrp V J :=
  fun g hg => mem_of_entry V J g fun i j => h (entry_mem_of V I g hg i j)

/- English proof (translation)
Introduce `a ha`. Unfold `idAt at ha`. Unfold `idOff`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢`. Introduce `u`.

Conclude with `ha.2 ⟨u.1, hPQ u.1 u.2⟩`.
-/
theorem idAt_le_idOff_compl (P Q : Pl D → Prop) (hPQ : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  unfold idAt at ha
  unfold idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  exact ha.2 ⟨u.1, hPQ u.1 u.2⟩

end GlobalTheory.LevelCut

namespace GlobalTheory.LevelCut

/- English proof (translation)
Introduce `D c v n _ _ G hG j' x hx`. Establish `hoff : x ∈ grpOff (c.V j') (fun w => w ∉ Set.range fun i => (G i).q.v)`. Use `congGrp_le (c.V j') (idAt_le_idOff_compl _ _ fun w hw hP => hw ?_) hx` and prove the remaining obligations. Take `⟨i, hi⟩` from `(hG.places w).mp hP`. Conclude with `⟨i, hi.symm⟩`.

Take `⟨a, ha, h, hsupp, hcomm, -, hxa, -⟩` from `GlobalTheory.SplitCut.prod_of_trivOff D (c.V j') (Fin n) (fun i => (G i).q.v) (fun i => (G i).q.e) hG.inj (fun i => ⟨(G i).q.split, (G i).q.above⟩) x hoff`. Establish `hperm : (Finset.univ.toList.map h).prod = (List.ofFn h).prod`. Rewrite using `[List.ofFn_eq_map]`. Use `List.Perm.prod_eq' ((List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (List.nodup_finRange n) (by ext i; simp)).map h) ?_` and prove the remaining obligations. Conclude with `List.Pairwise.map _ (fun i i' hii => hcomm i i' hii) (Finset.nodup_toList _)`.

Use `⟨h, hsupp, ?_⟩` and prove the remaining obligations. Establish `hP : (List.ofFn h).prod ∈ GfC (c.V j')`. Use `(GfC (c.V j')).list_prod_mem fun y hy => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.mem_ofFn.mp hy`. Conclude with `mem_GfC_of_supp (c.V j') _ (G i).q.above (h i) (hsupp i)`.

Establish `hxf : x ∈ GfC (c.V j')` using `mem_GfC_of_grpAt _ _ x hx`. Rewrite `hxa` using `[hperm]`. Establish `haf : a ∈ GfC (c.V j')`. Establish `: a = x * ((List.ofFn h).prod)⁻¹` using `by rw [hxa, mul_inv_cancel_right]`. Rewrite using `[this]`.

Conclude with `mul_mem hxf (inv_mem hP)`. Rewrite using `[hxa, eq_one_of_parts _ a haf ha, one_mul]`.
-/
theorem grpAt_eq_prod_local : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G →
    ∀ (j' : ℕ), ∀ x ∈ grpAt (c.V j') (· ∈ v.gP), ∃ xs : Fin n → GA D (c.V j'),
      (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) ∧ x = (List.ofFn xs).prod := by
  intro D c v n _ _ G hG j' x hx
  have hoff : x ∈ grpOff (c.V j') (fun w => w ∉ Set.range fun i => (G i).q.v) := by
    refine congGrp_le (c.V j') (idAt_le_idOff_compl _ _ fun w hw hP => hw ?_) hx
    obtain ⟨i, hi⟩ := (hG.places w).mp hP
    exact ⟨i, hi.symm⟩
  obtain ⟨a, ha, h, hsupp, hcomm, -, hxa, -⟩ := GlobalTheory.SplitCut.prod_of_trivOff D (c.V j') (Fin n) (fun i => (G i).q.v)
    (fun i => (G i).q.e) hG.inj (fun i => ⟨(G i).q.split, (G i).q.above⟩) x hoff
  have hperm : (Finset.univ.toList.map h).prod = (List.ofFn h).prod := by
    rw [List.ofFn_eq_map]
    refine List.Perm.prod_eq' ((List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (List.nodup_finRange n)
      (by ext i; simp)).map h) ?_
    exact List.Pairwise.map _ (fun i i' hii => hcomm i i' hii) (Finset.nodup_toList _)
  refine ⟨h, hsupp, ?_⟩
  have hP : (List.ofFn h).prod ∈ GfC (c.V j') := by
    refine (GfC (c.V j')).list_prod_mem fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact mem_GfC_of_supp (c.V j') _ (G i).q.above (h i) (hsupp i)
  have hxf : x ∈ GfC (c.V j') := mem_GfC_of_grpAt _ _ x hx
  rw [hperm] at hxa
  have haf : a ∈ GfC (c.V j') := by
    have : a = x * ((List.ofFn h).prod)⁻¹ := by rw [hxa, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hxf (inv_mem hP)
  rw [hxa, eq_one_of_parts _ a haf ha, one_mul]

end GlobalTheory.LevelCut
