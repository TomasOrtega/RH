import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemSupport

section Generic

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `h1 : f * (1 - f) = 0` using `by linear_combination -hf`. Establish `h2 : (1 - f) * f = 0` using `by linear_combination -hf`. Establish `h3 : (1 - f) * (1 - f) = 1 - f` using `by linear_combination hf`. Simplify using `only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hf, h1, h2, h3, zero_smul, add_zero, zero_add]`.
-/
theorem mix_mul {f : A} (hf : f * f = f) (a b c d : Matrix n n A) :
    (f • a + (1 - f) • b) * (f • c + (1 - f) • d) = f • (a * c) + (1 - f) • (b * d) := by
  have h1 : f * (1 - f) = 0 := by linear_combination -hf
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hf, h1, h2, h3, zero_smul,
    add_zero, zero_add]

omit [Fintype n] [DecidableEq n] in
/- English proof (translation)
Rewrite using `[← add_smul, add_sub_cancel, one_smul]`.
-/
theorem mix_self (f : A) (a : Matrix n n A) : f • a + (1 - f) • a = a := by
  rw [← add_smul, add_sub_cancel, one_smul]

/- English proof (translation)
Rewrite using `[hb, hc, add_comm ((1 - f) • a), mix_mul hf, mul_one, one_mul, mix_self]`.
-/
theorem mix_split {f : A} (hf : f * f = f) {a b c : Matrix n n A} (hb : b = f • a + (1 - f) • (1 : Matrix n n A))
    (hc : c = (1 - f) • a + f • (1 : Matrix n n A)) : b * c = a := by
  rw [hb, hc, add_comm ((1 - f) • a), mix_mul hf, mul_one, one_mul, mix_self]

omit [Fintype n] in
/- English proof (translation)
Establish `h2 : (1 - f) * f = 0` using `by linear_combination -hf`. Establish `h3 : (1 - f) * (1 - f) = 1 - f` using `by linear_combination hf`. Rewrite using `[hb, smul_add, smul_smul, smul_smul, h2, h3, zero_smul, zero_add]`.
-/
theorem smul_mix {f : A} (hf : f * f = f) {a b : Matrix n n A} (hb : b = f • a + (1 - f) • (1 : Matrix n n A)) :
    (1 - f) • b = (1 - f) • (1 : Matrix n n A) := by
  have h2 : (1 - f) * f = 0 := by linear_combination -hf
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  rw [hb, smul_add, smul_smul, smul_smul, h2, h3, zero_smul, zero_add]

def piece {f : A} (hf : f * f = f) (g : GL n A) : GL n A where
  val := f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)
  inv := f • ((g⁻¹ : GL n A) : Matrix n n A) + (1 - f) • (1 : Matrix n n A)
  val_inv := by rw [mix_mul hf, Units.mul_inv, one_mul, mix_self]
  inv_val := by rw [mix_mul hf, Units.inv_mul, one_mul, mix_self]

/- English proof (translation)
Establish `hg' : Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J` using `hg`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT σ (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) * J * (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) = J`. Establish `h1 : Formalism.UG.cT σ (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) = f • Formalism.UG.cT σ (g : Matrix n n A) + (1 - f) • Formalism.UG.cT σ (1 : Matrix n n A)`. Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ]`.

Rewrite using `[h1, Formalism.UG.cT_one]`. Use `conv_lhs => rw [← mix_self f J]`. Rewrite using `[mix_mul hf, mix_mul hf, hg', one_mul, mul_one, mix_self]`.
-/
theorem piece_mem (σ : A →+* A) (J : Matrix n n A) {f : A} (hf : f * f = f) (hσ : σ f = f) {g : GL n A}
    (hg : g ∈ Formalism.UG.UJ σ J) : piece hf g ∈ Formalism.UG.UJ σ J := by
  have hg' : Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  change Formalism.UG.cT σ (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) * J *
    (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) = J
  have h1 : Formalism.UG.cT σ (f • (g : Matrix n n A) + (1 - f) • (1 : Matrix n n A)) =
      f • Formalism.UG.cT σ (g : Matrix n n A) + (1 - f) • Formalism.UG.cT σ (1 : Matrix n n A) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, map_sub, map_one, hσ]
  rw [h1, Formalism.UG.cT_one]
  conv_lhs => rw [← mix_self f J]
  rw [mix_mul hf, mix_mul hf, hg', one_mul, mul_one, mix_self]

/- English proof (translation)
Rewrite using `[← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Apply the tactic sequence `constructor <;> intro h <;> linear_combination -h`.
-/
theorem supp_iff (f : A) (g : Matrix n n A) :
    (∀ i j, f * (g - 1) i j = (g - 1) i j) ↔ (1 - f) • g = (1 - f) • (1 : Matrix n n A) := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  constructor <;> intro h <;> linear_combination -h

/- English proof (translation)
Establish `e1 : f • (g - 1) = g - 1` using `Matrix.ext hg`. Establish `e2 : f' • (g' - 1) = g' - 1` using `Matrix.ext hg'`. Establish `e3 : (g - 1) * (g' - 1) = 0`. Rewrite using `[← e1, ← e2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, zero_smul]`. Establish `e4 : (g' - 1) * (g - 1) = 0`.

Rewrite using `[← e1, ← e2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm f' f, h, zero_smul]`. Establish `: g * g' - g' * g = (g - 1) * (g' - 1) - (g' - 1) * (g - 1)` using `by noncomm_ring`. Rewrite using `[← sub_eq_zero, this, e3, e4, sub_zero]`.
-/
theorem commute_of_supp {f f' : A} (h : f * f' = 0) {g g' : Matrix n n A}
    (hg : ∀ i j, f * (g - 1) i j = (g - 1) i j) (hg' : ∀ i j, f' * (g' - 1) i j = (g' - 1) i j) :
    g * g' = g' * g := by
  have e1 : f • (g - 1) = g - 1 := Matrix.ext hg
  have e2 : f' • (g' - 1) = g' - 1 := Matrix.ext hg'
  have e3 : (g - 1) * (g' - 1) = 0 := by
    rw [← e1, ← e2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h, zero_smul]
  have e4 : (g' - 1) * (g - 1) = 0 := by
    rw [← e1, ← e2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm f' f, h, zero_smul]
  have : g * g' - g' * g = (g - 1) * (g' - 1) - (g' - 1) * (g - 1) := by noncomm_ring
  rw [← sub_eq_zero, this, e3, e4, sub_zero]

end Generic

variable {D : D7}

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_mul, Units.val_mul]`.
-/
theorem mt_mul (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul, Units.val_mul]

/- English proof (translation)
Unfold `Formalism.L2.Theta.mt`. Rewrite using `[map_one, Units.val_one]`.
-/
theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one, Units.val_one]

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext e)`.
-/
theorem mt_inj (V : HSp D) {g h : GA D V} (e : mt V g = mt V h) : g = h :=
  Subtype.ext (Units.ext e)

/- English proof (translation)
The claim follows from `supp_iff f _`.
-/
theorem suppF_iff (V : HSp D) (f : Formalism.L2.Theta.AE D) (g : GA D V) :
    SuppF V f g ↔ (1 - f) • mt V g = (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
  supp_iff f _

def suppGroup (V : HSp D) (f : Formalism.L2.Theta.AE D) : Subgroup (GA D V) where
  carrier := {g | SuppF V f g}
  one_mem' := by
    change SuppF V f 1
    rw [suppF_iff, mt_one]
  mul_mem' := by
    intro a b ha hb
    change SuppF V f _ at ha hb ⊢
    rw [suppF_iff] at ha hb ⊢
    rw [mt_mul, ← Matrix.smul_mul, ha, Matrix.smul_mul, one_mul, hb]
  inv_mem' := by
    intro a ha
    change SuppF V f _ at ha ⊢
    rw [suppF_iff] at ha ⊢
    have h := congrArg (· * mt V a⁻¹) ha
    simp only [Matrix.smul_mul, one_mul] at h
    rw [← h, ← mt_mul, mul_inv_cancel, mt_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨piece hf g.1, piece_mem _ _ hf hc g.2⟩, rfl⟩`.
-/
theorem exists_piece (V : HSp D) {f : Formalism.L2.Theta.AE D} (hf : f * f = f) (hc : cA D f = f) (g : GA D V) :
    ∃ g₁ : GA D V, mt V g₁ = f • mt V g + (1 - f) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Theta.AE D)) :=
  ⟨⟨piece hf g.1, piece_mem _ _ hf hc g.2⟩, rfl⟩

/- English proof (translation)
Establish `h3 : (1 - f) * (1 - f) = 1 - f` using `by linear_combination hf`. Take `⟨g₁, e₁⟩` from `exists_piece V hf hc g`. Take `⟨g₂, e₂⟩` from `exists_piece V h3 (by rw [map_sub, map_one, hc]) g`. Establish `s₁` using `(suppF_iff V f g₁).2 (smul_mix hf e₁)`. Establish `s₂` using `(suppF_iff V (1 - f) g₂).2 (smul_mix h3 e₂)`.

Rewrite `e₂` using `[sub_sub_cancel]`. Establish `e4` using `mix_split hf e₁ e₂`. Establish `e5` using `mt_mul V g₁ g₂`. Conclude with `⟨g₁, g₂, s₁, s₂, mt_inj V (e5.trans e4).symm⟩`.
-/
theorem exists_split (V : HSp D) {f : Formalism.L2.Theta.AE D} (hf : f * f = f) (hc : cA D f = f) (g : GA D V) :
    ∃ g₁ g₂, SuppF V f g₁ ∧ SuppF V (1 - f) g₂ ∧ g = g₁ * g₂ := by
  have h3 : (1 - f) * (1 - f) = 1 - f := by linear_combination hf
  obtain ⟨g₁, e₁⟩ := exists_piece V hf hc g
  obtain ⟨g₂, e₂⟩ := exists_piece V h3 (by rw [map_sub, map_one, hc]) g
  have s₁ := (suppF_iff V f g₁).2 (smul_mix hf e₁)
  have s₂ := (suppF_iff V (1 - f) g₂).2 (smul_mix h3 e₂)
  rw [sub_sub_cancel] at e₂
  have e4 := mix_split hf e₁ e₂
  have e5 := mt_mul V g₁ g₂
  exact ⟨g₁, g₂, s₁, s₂, mt_inj V (e5.trans e4).symm⟩

/- English proof (translation)
Establish `h1 : mt V g * mt V g' = mt V g' * mt V g` using `commute_of_supp h hg hg'`. Rewrite `h1` using `[← mt_mul, ← mt_mul]`. Conclude with `(commute_iff_eq g g').2 (mt_inj V h1)`.
-/
theorem commute_of_suppF (V : HSp D) {f f' : Formalism.L2.Theta.AE D} {g g' : GA D V} (h : f * f' = 0)
    (hg : SuppF V f g) (hg' : SuppF V f' g') : Commute g g' := by
  have h1 : mt V g * mt V g' = mt V g' * mt V g := commute_of_supp h hg hg'
  rw [← mt_mul, ← mt_mul] at h1
  exact (commute_iff_eq g g').2 (mt_inj V h1)

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Establish `h` using `congrArg (infPart D) (hg i j)`. Rewrite `h` using `[map_mul, hf, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero]`. Express the relevant statement in the definitionally equal form `infPart D (mt V g i j) = (1 : Matrix _ _ _) i j`. Rewrite using `[h, Matrix.one_apply, Matrix.one_apply]`.

Use `split_ifs`. Conclude with `map_one _`. Conclude with `map_zero _`.
-/
theorem mem_GfC_of_suppF (V : HSp D) {f : Formalism.L2.Theta.AE D} (hf : infPart D f = 0) {g : GA D V}
    (hg : SuppF V f g) : g ∈ GfC V := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := congrArg (infPart D) (hg i j)
  rw [map_mul, hf, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at h
  change infPart D (mt V g i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

structure Comp (D : D7) (Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) : Prop where
  ext : ∀ z, infPart D z = 0 → Φ z = 0 → z = 0
  surj : ∀ s, ∃ z, infPart D z = 0 ∧ Φ z = s
  inc : ∀ x, Φ (incA D x) = algebraMap _ _ x
  int : ∀ z, finPart D z ∈ intAE D ↔ ∀ Q, Φ z Q ∈ Q.adicCompletionIntegers D.host.E
  base : ∀ (a : AF D.host.F) Q, Φ (algebraMap _ _ a) Q =
    GlobalTheory.AdeleBaseChange.locMap D.host.F Q (a.2 (Q.under (𝓞 D.host.F)))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `: intAE D ≤ (Formalism.L2.DIV.RInt D.host.F D.host.E).toAddSubgroup.comap (Formalism.IndefR.Lev.swapAE D).toAddMonoidHom`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, rfl⟩`.

Conclude with `Formalism.UG.P.levelaf_tmul_mem x ha`. Conclude with `this hz`. Introduce `hz`. Take `⟨m, g, hg⟩` from `Module.Finite.exists_fin (R := ℤ) (M := 𝓞 D.host.E)`. Take `⟨r, hr, e⟩` from `Formalism.UG.P.levelaf_decomp g hg hz`.

Establish `: z = ∑ j, r j ⊗ₜ[D.host.F] (g j : D.host.E)`. Apply `(Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Conclude with `e`. Rewrite using `[this]`.

Conclude with `sum_mem fun j _ => AddSubgroup.subset_closure ⟨r j, hr j, g j, rfl⟩`.
-/
theorem mem_intAE_iff (z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ intAE D ↔ Formalism.IndefR.Lev.swapAE D z ∈ Formalism.L2.DIV.RInt D.host.F D.host.E := by
  constructor
  · intro hz
    have : intAE D ≤ (Formalism.L2.DIV.RInt D.host.F D.host.E).toAddSubgroup.comap
        (Formalism.IndefR.Lev.swapAE D).toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨a, ha, x, rfl⟩
      exact Formalism.UG.P.levelaf_tmul_mem x ha
    exact this hz
  · intro hz
    obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 D.host.E)
    obtain ⟨r, hr, e⟩ := Formalism.UG.P.levelaf_decomp g hg hz
    have : z = ∑ j, r j ⊗ₜ[D.host.F] (g j : D.host.E) := by
      apply (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective
      rw [map_sum]
      exact e
    rw [this]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨r j, hr j, g j, rfl⟩

/- English proof (translation)
Take `⟨ι, hι⟩` from `GlobalTheory.AdeleBaseChange.exists_toAd D.host.F D.host.E`. Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Establish `he1 : ∀ z, (e z).1 = infPart D z` using `fun z => (he z).1`. Establish `he2 : ∀ z, (e z).2 = finPart D z` using `fun z => (he z).2`. Establish `hb : Function.Bijective (Formalism.IndefR.Lev.swapAE D)` using `(Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).bijective`.

Use `⟨ι.comp ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)), fun z h1 h2 => ?_, fun s => ?_, fun x => ?_, fun z => ?_, fun a Q => ?_⟩` and prove the remaining obligations. Establish `h3 : finPart D z = 0` using `hb.1 (GlobalTheory.AdeleBaseChange.map_injective hι (by`. Rewrite using `[map_zero, map_zero]`. Conclude with `h2))`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Conclude with `Prod.ext ((he1 z).trans h1) ((he2 z).trans h3)`. Take `⟨y, rfl⟩` from `GlobalTheory.AdeleBaseChange.map_surjective hι s`. Take `⟨y, rfl⟩` from `hb.2 y`. Take `⟨z, hz⟩` from `e.surjective (0, y)`.

Use `⟨z, by rw [← he1, hz], ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ι (Formalism.IndefR.Lev.swapAE D (finPart D z)) = _`. Rewrite using `[← he2, hz]`. Conclude with `GlobalTheory.AdeleBaseChange.map_tmul_one hι x`. Rewrite using `[mem_intAE_iff]`.

Conclude with `⟨fun h => GlobalTheory.AdeleBaseChange.map_mem_int hι h, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι h⟩`. Express the relevant statement in the definitionally equal form `ι ((1 : D.host.E) ⊗ₜ[D.host.F] a.2) Q = _`. Rewrite using `[hι, map_one, one_mul]`. Both sides reduce to the same expression.
-/
theorem exists_comp (D : D7) : ∃ Φ, Comp D Φ := by
  obtain ⟨ι, hι⟩ := GlobalTheory.AdeleBaseChange.exists_toAd D.host.F D.host.E
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  have hb : Function.Bijective (Formalism.IndefR.Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).bijective
  refine ⟨ι.comp ((Formalism.IndefR.Lev.swapAE D).comp (finPart D)), fun z h1 h2 => ?_, fun s => ?_, fun x => ?_,
    fun z => ?_, fun a Q => ?_⟩
  · have h3 : finPart D z = 0 := hb.1 (GlobalTheory.AdeleBaseChange.map_injective hι (by
      rw [map_zero, map_zero]; exact h2))
    apply e.injective
    rw [map_zero]
    exact Prod.ext ((he1 z).trans h1) ((he2 z).trans h3)
  · obtain ⟨y, rfl⟩ := GlobalTheory.AdeleBaseChange.map_surjective hι s
    obtain ⟨y, rfl⟩ := hb.2 y
    obtain ⟨z, hz⟩ := e.surjective (0, y)
    refine ⟨z, by rw [← he1, hz], ?_⟩
    change ι (Formalism.IndefR.Lev.swapAE D (finPart D z)) = _
    rw [← he2, hz]
  · exact GlobalTheory.AdeleBaseChange.map_tmul_one hι x
  · rw [mem_intAE_iff]
    exact ⟨fun h => GlobalTheory.AdeleBaseChange.map_mem_int hι h, fun h => GlobalTheory.AdeleBaseChange.mem_int_of_map hι h⟩
  · change ι ((1 : D.host.E) ⊗ₜ[D.host.F] a.2) Q = _
    rw [hι, map_one, one_mul]
    rfl

def IsDelta (Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) : Prop :=
  infPart D e = 0 ∧ Φ e P = 1 ∧ ∀ Q, Q ≠ P → Φ e Q = 0

def Comparison₂ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) : Prop :=
  ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)

def cO (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cO_coe (x : 𝓞 D.host.E) : (cO D x : D.host.E) = star (x : D.host.E) := rfl

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[cO_coe, cO_coe, star_star]`.
-/
theorem cO_cO (x : 𝓞 D.host.E) : cO D (cO D x) = x := by
  apply RingOfIntegers.ext
  rw [cO_coe, cO_coe, star_star]

def cP (P : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.E) :=
  HeightOneSpectrum.comap (cO D).toRingHom (cO D).surjective P

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_cP (P : HeightOneSpectrum (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (cP P).asIdeal ↔ cO D x ∈ P.asIdeal := Iff.rfl

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)`.
-/
theorem eq_of_le {P Q : HeightOneSpectrum (𝓞 D.host.E)} (h : P.asIdeal ≤ Q.asIdeal) : P = Q :=
  HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(eq_of_le fun x hx => ?_).symm` and prove the remaining obligations. Take `⟨c, hc, e⟩` from `h _ ((mem_cP P x).1 hx)`. Establish `: c = x`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[e, cO_coe, star_star]`. Conclude with `this ▸ hc`. Introduce and unpack `rfl c hc`. Conclude with `⟨cO D c, by rw [mem_cP, cO_cO]; exact hc, rfl⟩`.
-/
theorem isConjPl_iff (P P' : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P P' ↔ P' = cP P := by
  constructor
  · intro h
    refine (eq_of_le fun x hx => ?_).symm
    obtain ⟨c, hc, e⟩ := h _ ((mem_cP P x).1 hx)
    have : c = x := by
      apply RingOfIntegers.ext
      rw [e, cO_coe, star_star]
    exact this ▸ hc
  · rintro rfl c hc
    exact ⟨cO D c, by rw [mem_cP, cO_cO]; exact hc, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = a ⊗ₜ[D.host.F] 1`. Rewrite using `[map_one]`.
-/
theorem cA_algebraMap (a : AF D.host.F) :
    cA D (algebraMap _ (Formalism.L2.Theta.AE D) a) = algebraMap _ (Formalism.L2.Theta.AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = a ⊗ₜ[D.host.F] 1
  rw [map_one]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero, and_self]`. Consider the case `tmul a x => exact ⟨rfl, rfl⟩`. Consider the case `add a b ha hb => simp only [map_add, ha.1, ha.2, hb.1, hb.2, and_self]`.
-/
theorem parts_cA (z : Formalism.L2.Theta.AE D) :
    infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) ∧
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, and_self]
  | tmul a x => exact ⟨rfl, rfl⟩
  | add a b ha hb => simp only [map_add, ha.1, ha.2, hb.1, hb.2, and_self]

/- English proof (translation)
Rewrite using `[(parts_cA z).2]`. Establish `: intAE D ≤ (intAE D).comap (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig).toAddMonoidHom`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨a, ha, cO D x, rfl⟩`.

Conclude with `this hz`.
-/
theorem finPart_cA_mem {z : Formalism.L2.Theta.AE D} (hz : finPart D z ∈ intAE D) : finPart D (cA D z) ∈ intAE D := by
  rw [(parts_cA z).2]
  have : intAE D ≤ (intAE D).comap (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig).toAddMonoidHom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, ha, cO D x, rfl⟩
  exact this hz

/- English proof (translation)
Introduce `x hx`. Establish `e1 : cA D (e * incA D ((cO D x : D.host.E)⁻¹)) = cA D e * incA D ((x : D.host.E)⁻¹)`. Rewrite using `[map_mul, cA_incA, cO_coe, star_inv₀, star_star]`. Rewrite using `[mem_cP, h _ (by simpa using hx), ← e1]`. Use `not_congr ⟨finPart_cA_mem, fun h => ?_⟩` and prove the remaining obligations.

Use `finPart_cA_mem h` as an intermediate fact. Rewrite `this` using `[cA_cA]`. Then use the resulting hypothesis.
-/
theorem Comparison₂.conj {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (h : Comparison₂ P e) :
    Comparison₂ (cP P) (cA D e) := by
  intro x hx
  have e1 : cA D (e * incA D ((cO D x : D.host.E)⁻¹)) = cA D e * incA D ((x : D.host.E)⁻¹) := by
    rw [map_mul, cA_incA, cO_coe, star_inv₀, star_star]
  rw [mem_cP, h _ (by simpa using hx), ← e1]
  refine not_congr ⟨finPart_cA_mem, fun h => ?_⟩
  have := finPart_cA_mem h
  rwa [cA_cA] at this

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀, ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E), not_lt]`. Use `inv_le_one₀ (zero_lt_iff.2 ?_)` and prove the remaining obligations. Rewrite using `[Ne, Valuation.zero_iff]`. Conclude with `hx` after adjusting the coercions.
-/
theorem inv_mem_iff (Q : HeightOneSpectrum (𝓞 D.host.E)) {x : 𝓞 D.host.E} (hx : x ≠ 0) :
    algebraMap D.host.E (Q.adicCompletion D.host.E) ((x : D.host.E)⁻¹) ∈ Q.adicCompletionIntegers D.host.E ↔
      x ∉ Q.asIdeal := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E), not_lt]
  refine inv_le_one₀ (zero_lt_iff.2 ?_)
  rw [Ne, Valuation.zero_iff]
  exact_mod_cast hx

section

variable {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem ev_mul (a b : Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (a * b) Q = Φ a Q * Φ b Q := by rw [map_mul]; rfl

/- English proof (translation)
Rewrite using `[map_add]`. Both sides reduce to the same expression.
-/
theorem ev_add (a b : Formalism.L2.Theta.AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ (a + b) Q = Φ a Q + Φ b Q := by rw [map_add]; rfl

/- English proof (translation)
Rewrite using `[map_zero]`. Both sides reduce to the same expression.
-/
theorem ev_zero (Q : HeightOneSpectrum (𝓞 D.host.E)) : Φ 0 Q = 0 := by rw [map_zero]; rfl

variable (hΦ : Comp D Φ)
include hΦ

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `hΦ.ext _ (by rw [RingHom.map_sub, h1, sub_self]) ?_` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `FiniteAdeleRing.ext _ h2`.
-/
theorem Comp.ext' {a b : Formalism.L2.Theta.AE D} (h1 : infPart D a = infPart D b) (h2 : ∀ Q, Φ a Q = Φ b Q) : a = b := by
  rw [← sub_eq_zero]
  refine hΦ.ext _ (by rw [RingHom.map_sub, h1, sub_self]) ?_
  rw [map_sub, sub_eq_zero]
  exact FiniteAdeleRing.ext _ h2

/- English proof (translation)
Take `⟨z, h1, h2⟩` from `hΦ.surj (singleV D.host.E P 1)`. Use `⟨z, h1, ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`. Conclude with `Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.E) => w.adicCompletion D.host.E) P 1`. Rewrite using `[h2]`.

Conclude with `Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.E) => w.adicCompletion D.host.E) hQ 1`.
-/
theorem exists_delta (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ e, IsDelta Φ P e := by
  classical
  obtain ⟨z, h1, h2⟩ := hΦ.surj (singleV D.host.E P 1)
  refine ⟨z, h1, ?_, fun Q hQ => ?_⟩
  · rw [h2]; exact Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.E) => w.adicCompletion D.host.E) P 1
  · rw [h2]; exact Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.E) => w.adicCompletion D.host.E) hQ 1

/- English proof (translation)
Use `hΦ.ext' (h.1.trans h'.1.symm) fun Q => ?_` and prove the remaining obligations. Distinguish the cases in `hQ : Q = P`. Rewrite using `[hQ, h.2.1, h'.2.1]`. Rewrite using `[h.2.2 Q hQ, h'.2.2 Q hQ]`.
-/
theorem delta_unique {P : HeightOneSpectrum (𝓞 D.host.E)} {e e' : Formalism.L2.Theta.AE D} (h : IsDelta Φ P e)
    (h' : IsDelta Φ P e') : e = e' := by
  refine hΦ.ext' (h.1.trans h'.1.symm) fun Q => ?_
  by_cases hQ : Q = P
  · rw [hQ, h.2.1, h'.2.1]
  · rw [h.2.2 Q hQ, h'.2.2 Q hQ]

/- English proof (translation)
Use `delta_unique hΦ ⟨by rw [map_mul, h.1, zero_mul], by rw [ev_mul, h.2.1, one_mul], fun Q hQ => ?_⟩ h` and prove the remaining obligations. Rewrite using `[ev_mul, h.2.2 Q hQ, zero_mul]`.
-/
theorem delta_idem {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (h : IsDelta Φ P e) :
    e * e = e := by
  refine delta_unique hΦ ⟨by rw [map_mul, h.1, zero_mul], by rw [ev_mul, h.2.1, one_mul], fun Q hQ => ?_⟩ h
  rw [ev_mul, h.2.2 Q hQ, zero_mul]

/- English proof (translation)
Rewrite using `[hΦ.int, not_forall]`. Use `exists_congr fun Q => ?_` and prove the remaining obligations. Rewrite using `[ev_mul, hΦ.inc]`. Distinguish the cases in `h0 : Φ e Q = 0`. Rewrite using `[h0, zero_mul]`.

Conclude with `iff_of_false (fun h => h (zero_mem _)) (fun h => h.1 rfl)`. Establish `h1 : Φ e Q = 1` using `mul_left_cancel₀ h0 (by rw [← ev_mul, he, mul_one])`. Rewrite using `[h1, one_mul]`. Conclude with `((inv_mem_iff Q hx).not.trans not_not).trans (and_iff_right one_ne_zero).symm`.
-/
theorem not_int_iff {e : Formalism.L2.Theta.AE D} (he : e * e = e) {x : 𝓞 D.host.E} (hx : x ≠ 0) :
    finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D ↔ ∃ Q, Φ e Q ≠ 0 ∧ x ∈ Q.asIdeal := by
  rw [hΦ.int, not_forall]
  refine exists_congr fun Q => ?_
  rw [ev_mul, hΦ.inc]
  by_cases h0 : Φ e Q = 0
  · rw [h0, zero_mul]
    exact iff_of_false (fun h => h (zero_mem _)) (fun h => h.1 rfl)
  · have h1 : Φ e Q = 1 := mul_left_cancel₀ h0 (by rw [← ev_mul, he, mul_one])
    rw [h1, one_mul]
    exact ((inv_mem_iff Q hx).not.trans not_not).trans (and_iff_right one_ne_zero).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ∀ Q, Φ e Q ≠ 0 → Q = P` using `fun Q hQ => eq_of_le fun x hx => by`. Distinguish the cases in `hx0 : x = 0`. Rewrite using `[hx0]`.

Conclude with `zero_mem _`. Conclude with `(h x hx0).2 ((not_int_iff hΦ he hx0).2 ⟨Q, hQ, hx⟩)`. Use `⟨h0, ?_, fun Q hQ => by_contra fun h2 => hQ (h1 Q h2)⟩` and prove the remaining obligations. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot`. Take `⟨Q, hQ, -⟩` from `(not_int_iff hΦ he hx0).1 ((h x hx0).1 hx)`.

Rewrite `hQ` using `[h1 Q hQ]`. Conclude with `mul_left_cancel₀ hQ (by rw [← ev_mul, he, mul_one])`. Introduce `h x hx`. Rewrite using `[not_int_iff hΦ he hx]`. Use `⟨fun hP => ⟨P, by rw [h.2.1]; exact one_ne_zero, hP⟩, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨Q, h1, h2⟩`. Establish `: Q = P` using `by_contra fun h3 => h1 (h.2.2 Q h3)`. Conclude with `this ▸ h2`.
-/
theorem tie_iff {e : Formalism.L2.Theta.AE D} (he : e * e = e) (h0 : infPart D e = 0)
    (P : HeightOneSpectrum (𝓞 D.host.E)) : Comparison₂ P e ↔ IsDelta Φ P e := by
  constructor
  · intro h
    have h1 : ∀ Q, Φ e Q ≠ 0 → Q = P := fun Q hQ => eq_of_le fun x hx => by
      by_cases hx0 : x = 0
      · rw [hx0]; exact zero_mem _
      · exact (h x hx0).2 ((not_int_iff hΦ he hx0).2 ⟨Q, hQ, hx⟩)
    refine ⟨h0, ?_, fun Q hQ => by_contra fun h2 => hQ (h1 Q h2)⟩
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    obtain ⟨Q, hQ, -⟩ := (not_int_iff hΦ he hx0).1 ((h x hx0).1 hx)
    rw [h1 Q hQ] at hQ
    exact mul_left_cancel₀ hQ (by rw [← ev_mul, he, mul_one])
  · intro h x hx
    rw [not_int_iff hΦ he hx]
    refine ⟨fun hP => ⟨P, by rw [h.2.1]; exact one_ne_zero, hP⟩, ?_⟩
    rintro ⟨Q, h1, h2⟩
    have : Q = P := by_contra fun h3 => h1 (h.2.2 Q h3)
    exact this ▸ h2

/- English proof (translation)
Establish `he` using `delta_idem hΦ h`. Use `(tie_iff hΦ (by rw [← map_mul, he]) (by rw [(parts_cA e).1, h.1, map_zero]) _).1 ?_` and prove the remaining obligations. Conclude with `((tie_iff hΦ he h.1 P).2 h).conj`.
-/
theorem delta_conj {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (h : IsDelta Φ P e) :
    IsDelta Φ (cP P) (cA D e) := by
  have he := delta_idem hΦ h
  refine (tie_iff hΦ (by rw [← map_mul, he]) (by rw [(parts_cA e).1, h.1, map_zero]) _).1 ?_
  exact ((tie_iff hΦ he h.1 P).2 h).conj

/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `h`. Use `⟨TensorProduct.zero_tmul _ _, fun Q hQ => ?_, fun Q hQ => ?_⟩` and prove the remaining obligations. Substitute `hQ` using the available equality. Rewrite using `[hΦ.base]`. Conclude with `(congrArg _ h1).trans (map_one _)`.

Rewrite using `[hΦ.base]`. Conclude with `(congrArg _ (h0 _ hQ)).trans (map_zero _)`.
-/
theorem place_comp {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    infPart D (algebraMap _ (Formalism.L2.Theta.AE D) ε) = 0 ∧
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v → Φ (algebraMap _ _ ε) Q = 1) ∧
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) ≠ v → Φ (algebraMap _ _ ε) Q = 0) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  refine ⟨TensorProduct.zero_tmul _ _, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · subst hQ
    rw [hΦ.base]
    exact (congrArg _ h1).trans (map_one _)
  · rw [hΦ.base]
    exact (congrArg _ (h0 _ hQ)).trans (map_zero _)

end

/- English proof (translation)
Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Establish `: cO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Rewrite using `[cO_coe]`. Conclude with `(D.sp.cm.fixed _).2 ⟨x, rfl⟩`.

Express the relevant statement in the definitionally equal form `cO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ∈ P.asIdeal ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal`. Rewrite using `[this]`.
-/
theorem under_cP (P : HeightOneSpectrum (𝓞 D.host.E)) :
    (cP P).under (𝓞 D.host.F) = P.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  have : cO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := by
    apply RingOfIntegers.ext
    rw [cO_coe]
    exact (D.sp.cm.fixed _).2 ⟨x, rfl⟩
  change cO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) ∈ P.asIdeal ↔
    algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x ∈ P.asIdeal
  rw [this]

/- English proof (translation)
Establish `hle : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (cP P).asIdeal`. Introduce `x hx`. Take `⟨t, ht⟩` from `(D.sp.cm.fixed ((x : D.host.E) * star (x : D.host.E))).1 (by rw [star_mul, star_star])`. Establish `hint : IsIntegral ℤ t`. Rewrite using `[← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E) (algebraMap D.host.F D.host.E).injective]`.

Express the relevant statement in the definitionally equal form `IsIntegral ℤ (algebraMap D.host.F D.host.E t)`. Rewrite using `[ht]`. Conclude with `(x * cO D x).isIntegral_coe`. Establish `e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨t, hint⟩ = x * cO D x` using `RingOfIntegers.ext ht`. Establish `h1 : (⟨t, hint⟩ : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal`.

Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ hx`. Rewrite `h1` using `[h]`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h1`.

Rewrite `h1` using `[e]`. Conclude with `P.isPrime.mem_or_mem h1`. Conclude with `(Ideal.subset_union.1 hle).imp eq_of_le eq_of_le`.
-/
theorem eq_or_eq_cP {P Q : HeightOneSpectrum (𝓞 D.host.E)}
    (h : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)) : Q = P ∨ Q = cP P := by
  have hle : (Q.asIdeal : Set (𝓞 D.host.E)) ⊆ P.asIdeal ∪ (cP P).asIdeal := by
    intro x hx
    obtain ⟨t, ht⟩ := (D.sp.cm.fixed ((x : D.host.E) * star (x : D.host.E))).1
      (by rw [star_mul, star_star])
    have hint : IsIntegral ℤ t := by
      rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E) (algebraMap D.host.F D.host.E).injective]
      change IsIntegral ℤ (algebraMap D.host.F D.host.E t)
      rw [ht]
      exact (x * cO D x).isIntegral_coe
    have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ⟨t, hint⟩ = x * cO D x := RingOfIntegers.ext ht
    have h1 : (⟨t, hint⟩ : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [e]
      exact Ideal.mul_mem_right _ _ hx
    rw [h] at h1
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h1
    rw [e] at h1
    exact P.isPrime.mem_or_mem h1
  exact (Ideal.subset_union.1 hle).imp eq_of_le eq_of_le

/- English proof (translation)
Conclude with `⟨_, singleV D.host.F v 1, rfl, Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) v 1, fun w hw => Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) hw 1⟩`.
-/
theorem exists_placeIdem (v : HeightOneSpectrum (𝓞 D.host.F)) : ∃ ε, IsPlaceIdem D v ε := by
  classical
  exact ⟨_, singleV D.host.F v 1, rfl,
    Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) v 1,
    fun w hw => Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 D.host.F) => w.adicCompletion D.host.F) hw 1⟩

/- English proof (translation)
Take `⟨α, rfl, h1, h0⟩` from `h`. Take `⟨β, rfl, k1, k0⟩` from `h'`. Use `congr 1`. Use `FiniteAdeleRing.ext _ fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Conclude with `h1.trans k1.symm`. Conclude with `(h0 w hw).trans (k0 w hw).symm`.
-/
theorem placeIdem_unique {v : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v ε') : ε = ε' := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨β, rfl, k1, k0⟩ := h'
  congr 1
  refine FiniteAdeleRing.ext _ fun w => ?_
  by_cases hw : w = v
  · subst hw; exact h1.trans k1.symm
  · exact (h0 w hw).trans (k0 w hw).symm

section

variable {Φ : Formalism.L2.Theta.AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
include hΦ

/- English proof (translation)
Take `⟨h0, h1, h2⟩` from `place_comp hΦ h`. Use `hΦ.ext' (by rw [RingHom.map_mul, h0, zero_mul]) fun Q => ?_` and prove the remaining obligations. Rewrite using `[ev_mul]`. Distinguish the cases in `hQ : Q.under (𝓞 D.host.F) = v`. Rewrite using `[h1 Q hQ, one_mul]`.

Rewrite using `[h2 Q hQ, zero_mul]`.
-/
theorem place_idem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    algebraMap _ (Formalism.L2.Theta.AE D) ε * algebraMap _ _ ε = algebraMap _ _ ε := by
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ h
  refine hΦ.ext' (by rw [RingHom.map_mul, h0, zero_mul]) fun Q => ?_
  rw [ev_mul]
  by_cases hQ : Q.under (𝓞 D.host.F) = v
  · rw [h1 Q hQ, one_mul]
  · rw [h2 Q hQ, zero_mul]

/- English proof (translation)
Take `⟨h0, -, h2⟩` from `place_comp hΦ h`. Take `⟨-, -, k2⟩` from `place_comp hΦ h'`. Use `hΦ.ext' (by rw [RingHom.map_mul, h0, zero_mul, RingHom.map_zero]) fun Q => ?_` and prove the remaining obligations. Rewrite using `[ev_mul, ev_zero]`. Distinguish the cases in `hQ : Q.under (𝓞 D.host.F) = v`.

Rewrite using `[k2 Q (hQ ▸ hv), mul_zero]`. Rewrite using `[h2 Q hQ, zero_mul]`.
-/
theorem place_orth {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F} (h : IsPlaceIdem D v ε)
    (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') :
    algebraMap _ (Formalism.L2.Theta.AE D) ε * algebraMap _ _ ε' = 0 := by
  obtain ⟨h0, -, h2⟩ := place_comp hΦ h
  obtain ⟨-, -, k2⟩ := place_comp hΦ h'
  refine hΦ.ext' (by rw [RingHom.map_mul, h0, zero_mul, RingHom.map_zero]) fun Q => ?_
  rw [ev_mul, ev_zero]
  by_cases hQ : Q.under (𝓞 D.host.F) = v
  · rw [k2 Q (hQ ▸ hv), mul_zero]
  · rw [h2 Q hQ, zero_mul]

/- English proof (translation)
Take `⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩` from `h`. Use `(tie_iff hΦ h1 ?_ P).1 ht` and prove the remaining obligations. Establish `: e = (e + cA D e) * e` using `by linear_combination -h1 - h2`. Rewrite using `[this, h3, RingHom.map_mul, (place_comp hΦ hε).1, zero_mul]`.
-/
theorem delta_of_isIdemAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D} (h : IsIdemAt e P) :
    IsDelta Φ P e := by
  obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
  refine (tie_iff hΦ h1 ?_ P).1 ht
  have : e = (e + cA D e) * e := by linear_combination -h1 - h2
  rw [this, h3, RingHom.map_mul, (place_comp hΦ hε).1, zero_mul]

/- English proof (translation)
Break down `h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩` into its components or cases. Establish `hd` using `delta_of_isIdemAt hΦ h`. Take `⟨⟨-, h2, v, ε, hε, h3⟩, -⟩` from `h`. Use `⟨hd, ε, ?_, h3⟩` and prove the remaining obligations. Establish `h4 : Φ (cA D e) P = 0`.

Use `ev_mul (Φ := Φ) e (cA D e) P` as an intermediate fact. Rewrite `this` using `[h2, ev_zero, hd.2.1, one_mul, eq_comm]`. Then use the resulting hypothesis. Establish `h5 : P.under (𝓞 D.host.F) = v`. Assume the negation of the conclusion as `hv`. Use `(place_comp hΦ hε).2.2 P hv` as an intermediate fact.

Rewrite `this` using `[← h3, ev_add, h4, hd.2.1, add_zero]`. Conclude with `one_ne_zero this`. Conclude with `h5 ▸ hε`. Establish `hd` using `(tie_iff hΦ (place_idem hΦ hε) (place_comp hΦ hε).1 P).1 ht`. Use `⟨hd, ε, ?_, rfl⟩` and prove the remaining obligations.

Establish `h5 : P.under (𝓞 D.host.F) = v`. Assume the negation of the conclusion as `hv`. Conclude with `one_ne_zero (hd.2.1.symm.trans ((place_comp hΦ hε).2.2 P hv))`. Conclude with `h5 ▸ hε`.
-/
theorem of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f) :
    IsDelta Φ P e ∧ ∃ ε, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧ f = algebraMap _ _ ε := by
  rcases h with ⟨h, rfl⟩ | ⟨rfl, ⟨v, ε, hε, rfl⟩, ht⟩
  · have hd := delta_of_isIdemAt hΦ h
    obtain ⟨⟨-, h2, v, ε, hε, h3⟩, -⟩ := h
    refine ⟨hd, ε, ?_, h3⟩
    have h4 : Φ (cA D e) P = 0 := by
      have := ev_mul (Φ := Φ) e (cA D e) P
      rwa [h2, ev_zero, hd.2.1, one_mul, eq_comm] at this
    have h5 : P.under (𝓞 D.host.F) = v := by
      by_contra hv
      have := (place_comp hΦ hε).2.2 P hv
      rw [← h3, ev_add, h4, hd.2.1, add_zero] at this
      exact one_ne_zero this
    exact h5 ▸ hε
  · have hd := (tie_iff hΦ (place_idem hΦ hε) (place_comp hΦ hε).1 P).1 ht
    refine ⟨hd, ε, ?_, rfl⟩
    have h5 : P.under (𝓞 D.host.F) = v := by
      by_contra hv
      exact one_ne_zero (hd.2.1.symm.trans ((place_comp hΦ hε).2.2 P hv))
    exact h5 ▸ hε

/- English proof (translation)
Take `⟨e, he⟩` from `exists_delta hΦ P`. Take `⟨ε, hε⟩` from `exists_placeIdem (D := D) (P.under (𝓞 D.host.F))`. Take `⟨h0, h1, h2⟩` from `place_comp hΦ hε`. Establish `hi` using `delta_idem hΦ he`. Establish `ht` using `(tie_iff hΦ hi he.1 P).2 he`.

Distinguish the cases in `hc : cP P = P`. Use `⟨e, e, Or.inr ⟨rfl, ⟨_, ε, hε, delta_unique hΦ he ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => ?_⟩⟩, ht⟩⟩` and prove the remaining obligations. Conclude with `(eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc)`. Establish `he'` using `delta_conj hΦ he`. Use `⟨e, _, Or.inl ⟨⟨⟨hi, ?_, _, ε, hε, ?_⟩, ht⟩, rfl⟩⟩` and prove the remaining obligations.

Use `hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_` and prove the remaining obligations. Rewrite using `[ev_mul, ev_zero]`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[he'.2.2 Q (Ne.symm hc), mul_zero]`.

Rewrite using `[he.2.2 Q hQ, zero_mul]`. Use `hΦ.ext' (by rw [RingHom.map_add, he.1, he'.1, add_zero, h0]) fun Q => ?_` and prove the remaining obligations. Rewrite using `[ev_add]`. Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality.

Rewrite using `[he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]`. Distinguish the cases in `hQ' : Q = cP P`. Substitute `hQ'` using the available equality. Rewrite using `[he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP P)]`. Rewrite using `[he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP h).elim hQ hQ']`.
-/
theorem exists_isPrimeIdem (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ e f, IsPrimeIdem P e f := by
  obtain ⟨e, he⟩ := exists_delta hΦ P
  obtain ⟨ε, hε⟩ := exists_placeIdem (D := D) (P.under (𝓞 D.host.F))
  obtain ⟨h0, h1, h2⟩ := place_comp hΦ hε
  have hi := delta_idem hΦ he
  have ht := (tie_iff hΦ hi he.1 P).2 he
  by_cases hc : cP P = P
  · refine ⟨e, e, Or.inr ⟨rfl, ⟨_, ε, hε, delta_unique hΦ he ⟨h0, h1 P rfl, fun Q hQ => h2 Q fun h => ?_⟩⟩, ht⟩⟩
    exact (eq_or_eq_cP h).elim hQ fun h => hQ (h.trans hc)
  · have he' := delta_conj hΦ he
    refine ⟨e, _, Or.inl ⟨⟨⟨hi, ?_, _, ε, hε, ?_⟩, ht⟩, rfl⟩⟩
    · refine hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_
      rw [ev_mul, ev_zero]
      by_cases hQ : Q = P
      · subst hQ
        rw [he'.2.2 Q (Ne.symm hc), mul_zero]
      · rw [he.2.2 Q hQ, zero_mul]
    · refine hΦ.ext' (by rw [RingHom.map_add, he.1, he'.1, add_zero, h0]) fun Q => ?_
      rw [ev_add]
      by_cases hQ : Q = P
      · subst hQ
        rw [he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]
      · by_cases hQ' : Q = cP P
        · subst hQ'
          rw [he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP P)]
        · rw [he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP h).elim hQ hQ']

end

/- English proof (translation)
Introduce `D V`. Take `⟨Φ, hΦ⟩` from `exists_comp D`. Use `⟨fun f hf hc => ⟨⟨suppGroup V f, fun _ => Iff.rfl⟩, exists_split V hf hc, fun f' g g' h hg hg' => commute_of_suppF V h hg hg'⟩, exists_isPrimeIdem hΦ, fun P e f h => ?_, fun P P' e h hc => ?_⟩` and prove the remaining obligations. Take `⟨hd, ε, hε, rfl⟩` from `of_isPrimeIdem hΦ h`. Use `⟨place_idem hΦ hε, cA_algebraMap ε, fun g hg => mem_GfC_of_suppF V (place_comp hΦ hε).1 hg, fun e' f' h' => ?_, fun P' e' f' h' => ?_⟩` and prove the remaining obligations.

Take `⟨hd', ε', hε', rfl⟩` from `of_isPrimeIdem hΦ h'`. Conclude with `⟨delta_unique hΦ hd' hd, by rw [placeIdem_unique hε' hε]⟩`. Take `⟨-, ε', hε', rfl⟩` from `of_isPrimeIdem hΦ h'`. Distinguish the cases in `hv : P'.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)`. Rewrite `hε'` using `[hv]`.

Conclude with `Or.inr ⟨by rw [placeIdem_unique hε' hε], (eq_or_eq_cP hv).imp id (isConjPl_iff P P').2⟩`. Conclude with `Or.inl (place_orth hΦ hε hε' (Ne.symm hv))`. Rewrite using `[(isConjPl_iff P P').1 hc]`. Take `⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩` from `h`. Conclude with `⟨⟨by rw [← RingHom.map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩, Comparison₂.conj ht⟩`.
-/
theorem supported_group_and_prime_idempotents : ∀ {D : D7} (V : HSp D), (∀ f : Formalism.L2.Theta.AE D, f * f = f → cA D f = f → (∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g) ∧ (∀ g : GA D V, ∃ g₁ g₂, SuppF V f g₁ ∧ SuppF V (1 - f) g₂ ∧ g = g₁ * g₂) ∧ ∀ f' g g', f * f' = 0 → SuppF V f g → SuppF V f' g' → Commute g g') ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → f * f = f ∧ cA D f = f ∧ (∀ g, SuppF V f g → g ∈ GfC V) ∧ (∀ e' f', IsPrimeIdem P e' f' → e' = e ∧ f' = f) ∧ ∀ P' e' f', IsPrimeIdem P' e' f' → f * f' = 0 ∨ (f' = f ∧ (P' = P ∨ Formalism.IndefR.Lev.IsConjPl P P'))) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) P' e, IsIdemAt e P → Formalism.IndefR.Lev.IsConjPl P P' → IsIdemAt (cA D e) P' := by
  intro D V
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  refine ⟨fun f hf hc => ⟨⟨suppGroup V f, fun _ => Iff.rfl⟩, exists_split V hf hc,
    fun f' g g' h hg hg' => commute_of_suppF V h hg hg'⟩, exists_isPrimeIdem hΦ, fun P e f h => ?_,
    fun P P' e h hc => ?_⟩
  · obtain ⟨hd, ε, hε, rfl⟩ := of_isPrimeIdem hΦ h
    refine ⟨place_idem hΦ hε, cA_algebraMap ε, fun g hg => mem_GfC_of_suppF V (place_comp hΦ hε).1 hg,
      fun e' f' h' => ?_, fun P' e' f' h' => ?_⟩
    · obtain ⟨hd', ε', hε', rfl⟩ := of_isPrimeIdem hΦ h'
      exact ⟨delta_unique hΦ hd' hd, by rw [placeIdem_unique hε' hε]⟩
    · obtain ⟨-, ε', hε', rfl⟩ := of_isPrimeIdem hΦ h'
      by_cases hv : P'.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)
      · rw [hv] at hε'
        exact Or.inr ⟨by rw [placeIdem_unique hε' hε], (eq_or_eq_cP hv).imp id (isConjPl_iff P P').2⟩
      · exact Or.inl (place_orth hΦ hε hε' (Ne.symm hv))
  · rw [(isConjPl_iff P P').1 hc]
    obtain ⟨⟨h1, h2, v, ε, hε, h3⟩, ht⟩ := h
    exact ⟨⟨by rw [← RingHom.map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, hε, by rw [cA_cA, add_comm, h3]⟩,
      Comparison₂.conj ht⟩

end GlobalTheory.IdemSupport
