import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRedKerA

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence

section Form

variable {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (J : Matrix n n A)

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_left (s : A) (x y : n → A) : Formalism.UG.hform σ J (s • x) y = σ s * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_smul_right (s : A) (x y : n → A) : Formalism.UG.hform σ J x (s • y) = s * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hform_add_left (x x' y : n → A) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hform_add_right (x y y' : n → A) :
    Formalism.UG.hform σ J x (y + y') = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `[Formalism.UG.hform]`.
-/
theorem hform_zero_left (y : n → A) : Formalism.UG.hform σ J 0 y = 0 := by
  simp [Formalism.UG.hform]

/- English proof (translation)
Simplify using `[Formalism.UG.hform]`.
-/
theorem hform_zero_right (x : n → A) : Formalism.UG.hform σ J x 0 = 0 := by
  simp [Formalism.UG.hform]

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]`.
-/
theorem hform_sub_left (x x' y : n → A) :
    Formalism.UG.hform σ J (x - x') y = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

/- English proof (translation)
Simplify using `only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem hform_sub_right (x y y' : n → A) :
    Formalism.UG.hform σ J x (y - y') = Formalism.UG.hform σ J x y - Formalism.UG.hform σ J x y' := by
  simp only [Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/- English proof (translation)
Establish `key : ∀ u v : n → A, Formalism.UG.hform σ J u v = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ v)`. Introduce `u v`. Simplify using `only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]`. Establish `hσ : (fun i => σ ((M *ᵥ x) i)) = M.map σ *ᵥ (fun i => σ (x i))`. Use function extensionality and compare the values at `i`.

Simplify using `only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]`. Rewrite using `[key, key, hσ, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, mulVec_mulVec, mulVec_mulVec, show (M.map σ)ᵀ * J * M = J from hM]`.
-/
theorem hform_unit [DecidableEq n] (M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ u v : n → A, Formalism.UG.hform σ J u v = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  have hσ : (fun i => σ ((M *ᵥ x) i)) = M.map σ *ᵥ (fun i => σ (x i)) := by
    funext i
    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [key, key, hσ, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm,
    mulVec_mulVec, mulVec_mulVec, show (M.map σ)ᵀ * J * M = J from hM]

end Form

variable (I : AutInst)

abbrev Lq (w : HeightOneSpectrum (𝓞 I.E)) : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F) :=
  lamAf (F := I.F) (wLat0 I w)

/- English proof (translation)
Use `haveI : Fact (1 < p) := ⟨hp.one_lt⟩`. Establish `H0 : ∀ m ∈ wLat0 I w, (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (m i)) ∈ Lq I w := by`. Introduce `m hm`. Use `show _ ∈ Submodule.span _ _`. Conclude with `Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩`.

Establish `G0 : ∀ l ∈ I.L, (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (l i)) ∈ I.Lf := by`. Introduce `l hl`. Use `show _ ∈ Submodule.span _ _`. Conclude with `Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩`. Establish `hstab : ∀ z, z ∈ I.Lf ↔ I.fmat x *ᵥ z ∈ I.Lf` using `hx`.

Establish `hint : ∀ a : 𝓞 I.E, Formalism.UG.inclE (F` using `I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E := fun a => by show _ ∈ Subring.closure _`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)`. Establish `H1 : ∀ a ∈ w.asIdeal, ∀ z ∈ I.Lf, Formalism.UG.inclE (F` using `I.F) (Af I.F) (a : I.E) • z ∈ Lq I w := by`. Introduce `a ha z hz`. Unfold `AutInst.Lf lamAf at hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨⟨l, hl⟩, rfl⟩` from `hz`. Use `show Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ Lq I w`. Establish `e : Formalism.UG.inclE (F` using `I.F) (Af I.F) (a : I.E) • (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) = fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((a : I.E) • l) i) := by`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Rewrite using `[e]`. Conclude with `H0 _ (Submodule.subset_span ⟨a, ha, l, hl, rfl⟩)`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv => rw [smul_add]`. Conclude with `add_mem hu hv`. Consider the case `smul r u _ hu`. Rewrite using `[smul_comm]`.

Conclude with `Submodule.smul_mem _ r hu`. Establish `H2 : ∀ m ∈ wLat0 I w, I.fmat x *ᵥ (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (m i)) ∈ Lq I w := by`. Introduce `m hm`. Unfold `wLat0 at hm`. Proceed by induction on `hm using Submodule.span_induction with`.

Consider the case `mem z hz`. Take `⟨a, ha, l, hl, rfl⟩` from `hz`. Establish `e : (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (((a : I.E) • l) i)) = Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i) := by`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`.

Rewrite using `[e, Matrix.mulVec_smul]`. Conclude with `H1 a ha _ ((hstab _).1 (G0 l hl))`. Consider the case `zero`. Establish `e : (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[e, Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv`. Establish `e : (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) ((u + v) i)) = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) + fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (v i) := by`.

Use function extensionality and compare the values at `i`. Simplify using `[map_add]`. Rewrite using `[e, Matrix.mulVec_add]`. Conclude with `add_mem hu hv`. Consider the case `smul o u _ hu`.

Establish `e : (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) ((o • u) i)) = Formalism.UG.inclE (F := I.F) (Af I.F) (o : I.E) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i) := by`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.smul_apply, ← algebraMap_smul I.E o (u i), smul_eq_mul, map_mul]`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.mulVec_smul]`.

Conclude with `Submodule.smul_mem _ (⟨Formalism.UG.inclE (F := I.F) (Af I.F) (o : I.E), hint o⟩ : IntAf I.F I.E) hu`. Take `⟨b, ⟨hbL, hspan⟩, hb⟩` from `hR`. Establish `hbi : ∀ k, (I.fmat x - 1) *ᵥ (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (b k i)) ∈ Lq I w := by`. Introduce `k`. Establish `hk` using `hb k`.

Establish `hsum : (∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (b j i))) = fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (b k i) := by`. Rewrite using `[Finset.sum_eq_single k]`. Simplify using `[ZMod.val_one]`. Introduce `j _ hjk`. Simplify using `[Matrix.one_apply_ne hjk]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`. Rewrite `hk` using `[hsum]`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `hk`.

Introduce `y hy`. Unfold `AutInst.Lf lamAf at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨⟨l, hl⟩, rfl⟩` from `hz`.

Take `⟨c, hc⟩` from `hspan l hl`. Use `show (I.fmat x - 1) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ Lq I w`. Establish `hdec : (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (l i)) = (∑ k, ((c k : ℤ) : I.E ⊗[I.F] Af I.F) • (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (b k i))) + (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((l - ∑ k, (c k : I.E) • b k) i)) := by`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, map_sub, map_sum, map_mul, map_intCast]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hdec, Matrix.mulVec_add, Matrix.mulVec_sum]`. Use `add_mem (Submodule.sum_mem _ fun k _ => ?_) ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ (⟨((c k : ℤ) : I.E ⊗[I.F] Af I.F), intCast_mem _ (c k)⟩ : IntAf I.F I.E) (hbi k)`.

Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Conclude with `sub_mem (H2 _ hc) (H0 _ hc)`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add u v _ _ hu hv => rw [Matrix.mulVec_add]`.

Conclude with `add_mem hu hv`. Consider the case `smul r u _ hu => show (I.fmat x - 1) *ᵥ ((r : I.E ⊗[I.F] Af I.F) • u) ∈ _`. Rewrite using `[Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ r hu`.
-/
theorem stepA {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p)
    {m : ℕ} {x : I.Gf} (hx : x ∈ I.Kset) (hR : RedMat0 I w p x (1 : Matrix (Fin m) (Fin m) (ZMod p))) :
    ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ Lq I w := by
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  have H0 : ∀ m ∈ wLat0 I w, (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (m i)) ∈ Lq I w := by
    intro m hm
    show _ ∈ Submodule.span _ _
    exact Submodule.subset_span ⟨⟨m, hm⟩, rfl⟩
  have G0 : ∀ l ∈ I.L, (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ I.Lf := by
    intro l hl
    show _ ∈ Submodule.span _ _
    exact Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
  have hstab : ∀ z, z ∈ I.Lf ↔ I.fmat x *ᵥ z ∈ I.Lf := hx
  have hint : ∀ a : 𝓞 I.E, Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E := fun a => by
    show _ ∈ Subring.closure _
    exact Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)
  have H1 : ∀ a ∈ w.asIdeal, ∀ z ∈ I.Lf, Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • z ∈ Lq I w := by
    intro a ha z hz
    unfold AutInst.Lf lamAf at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨l, hl⟩, rfl⟩ := hz
      show Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ Lq I w
      have e : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) =
          fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((a : I.E) • l) i) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      rw [e]
      exact H0 _ (Submodule.subset_span ⟨a, ha, l, hl, rfl⟩)
    | zero => rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
    | smul r u _ hu =>
      rw [smul_comm]
      exact Submodule.smul_mem _ r hu
  have H2 : ∀ m ∈ wLat0 I w, I.fmat x *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (m i)) ∈ Lq I w := by
    intro m hm
    unfold wLat0 at hm
    induction hm using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, hl, rfl⟩ := hz
      have e : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (((a : I.E) • l) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i) := by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      rw [e, Matrix.mulVec_smul]
      exact H1 a ha _ ((hstab _).1 (G0 l hl))
    | zero =>
      have e : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
        funext i
        simp
      rw [e, Matrix.mulVec_zero]
      exact zero_mem _
    | add u v _ _ hu hv =>
      have e : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((u + v) i)) =
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i)) + fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (v i) := by
        funext i
        simp [map_add]
      rw [e, Matrix.mulVec_add]
      exact add_mem hu hv
    | smul o u _ hu =>
      have e : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((o • u) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) (o : I.E) • fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (u i) := by
        funext i
        rw [Pi.smul_apply, ← algebraMap_smul I.E o (u i), smul_eq_mul, map_mul]
        rfl
      rw [e, Matrix.mulVec_smul]
      exact Submodule.smul_mem _ (⟨Formalism.UG.inclE (F := I.F) (Af I.F) (o : I.E), hint o⟩ : IntAf I.F I.E) hu
  obtain ⟨b, ⟨hbL, hspan⟩, hb⟩ := hR
  have hbi : ∀ k, (I.fmat x - 1) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (b k i)) ∈ Lq I w := by
    intro k
    have hk := hb k
    have hsum : (∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j k).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (b j i))) = fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (b k i) := by
      rw [Finset.sum_eq_single k]
      · simp [ZMod.val_one]
      · intro j _ hjk
        simp [Matrix.one_apply_ne hjk]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hsum] at hk
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact hk
  intro y hy
  unfold AutInst.Lf lamAf at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    obtain ⟨c, hc⟩ := hspan l hl
    show (I.fmat x - 1) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) ∈ Lq I w
    have hdec : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (l i)) =
        (∑ k, ((c k : ℤ) : I.E ⊗[I.F] Af I.F) • (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (b k i))) +
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((l - ∑ k, (c k : I.E) • b k) i)) := by
      funext i
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, map_sub, map_sum,
        map_mul, map_intCast]
      ring
    rw [hdec, Matrix.mulVec_add, Matrix.mulVec_sum]
    refine add_mem (Submodule.sum_mem _ fun k _ => ?_) ?_
    · rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ (⟨((c k : ℤ) : I.E ⊗[I.F] Af I.F), intCast_mem _ (c k)⟩ : IntAf I.F I.E) (hbi k)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_mem (H2 _ hc) (H0 _ hc)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add u v _ _ hu hv => rw [Matrix.mulVec_add]; exact add_mem hu hv
  | smul r u _ hu =>
    show (I.fmat x - 1) *ᵥ ((r : I.E ⊗[I.F] Af I.F) • u) ∈ _
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ r hu

def sigO : 𝓞 I.E ≃+* 𝓞 I.E := RingOfIntegers.mapRingEquiv (starRingAut : RingAut I.E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigO_coe (a : 𝓞 I.E) : ((sigO I a : 𝓞 I.E) : I.E) = star (a : I.E) := rfl

/- English proof (translation)
Conclude with `RingOfIntegers.ext (by rw [sigO_coe, sigO_coe, star_star])`.
-/
theorem sigO_sigO (a : 𝓞 I.E) : sigO I (sigO I a) = a := by
  exact RingOfIntegers.ext (by rw [sigO_coe, sigO_coe, star_star])

def wc (w : HeightOneSpectrum (𝓞 I.E)) : HeightOneSpectrum (𝓞 I.E) where
  asIdeal := w.asIdeal.comap (sigO I)
  isPrime := by have := w.isPrime; exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := Ideal.map_comap_of_surjective _ (sigO I).surjective w.asIdeal
    rw [← this, h, Ideal.map_bot]

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_wc (w : HeightOneSpectrum (𝓞 I.E)) (a : 𝓞 I.E) : a ∈ (wc I w).asIdeal ↔ sigO I a ∈ w.asIdeal := by
  exact Iff.rfl

/- English proof (translation)
Rewrite using `[mem_wc, sigO_sigO]`. Conclude with `ha`.
-/
theorem sig_mem_wc {w : HeightOneSpectrum (𝓞 I.E)} {a : 𝓞 I.E} (ha : a ∈ w.asIdeal) : sigO I a ∈ (wc I w).asIdeal := by
  rw [mem_wc, sigO_sigO]
  exact ha

/- English proof (translation)
Rewrite using `[mem_wc, map_natCast]`. Conclude with `h`.
-/
theorem natCast_mem_wc {w : HeightOneSpectrum (𝓞 I.E)} {p : ℕ} (h : (p : 𝓞 I.E) ∈ w.asIdeal) :
    (p : 𝓞 I.E) ∈ (wc I w).asIdeal := by
  rw [mem_wc, map_natCast]
  exact h

/- English proof (translation)
Establish `hv'` using `(I.L_dual v).1 hv`. Unfold `wLat0 at hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, y, hy, rfl⟩` from `hz`.

Take `⟨b, hb⟩` from `hv' y hy`. Use `⟨sigO I a * b, Ideal.mul_mem_right _ _ (sig_mem_wc I ha), ?_⟩` and prove the remaining obligations. Rewrite using `[hform_smul_left, ← hb]`. Use `show _ = algebraMap (𝓞 I.E) I.E (sigO I a * b)`. Rewrite using `[map_mul]`.

Conclude with `congrArg₂ (· * ·) (sigO_coe I a).symm rfl`. Consider the case `zero`. Conclude with `⟨0, Ideal.zero_mem _, by rw [hform_zero_left]; exact (map_zero (algebraMap (𝓞 I.E) I.E)).symm⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨c1, hc1, e1⟩` from `hx`.

Take `⟨c2, hc2, e2⟩` from `hy`. Conclude with `⟨c1 + c2, Ideal.add_mem _ hc1 hc2, by`. Rewrite using `[hform_add_left, e1, e2]`. Conclude with `(map_add (algebraMap (𝓞 I.E) I.E) c1 c2).symm⟩`. Consider the case `smul r x _ hx`.

Take `⟨c, hc, e⟩` from `hx`. Use `⟨sigO I r * c, Ideal.mul_mem_left _ _ hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul I.E r x, hform_smul_left, e]`. Use `show _ = algebraMap (𝓞 I.E) I.E (sigO I r * c)`. Rewrite using `[map_mul]`.

Conclude with `congrArg₂ (· * ·) (sigO_coe I r).symm rfl`.
-/
theorem hform_wLat0 {w : HeightOneSpectrum (𝓞 I.E)} {u : Fin I.n → I.E} (hu : u ∈ wLat0 I w) {v : Fin I.n → I.E}
    (hv : v ∈ I.L) : ∃ c ∈ (wc I w).asIdeal, Formalism.UG.hform (starRingEnd I.E) I.J u v = (c : I.E) := by
  have hv' := (I.L_dual v).1 hv
  unfold wLat0 at hu
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hz
    obtain ⟨b, hb⟩ := hv' y hy
    refine ⟨sigO I a * b, Ideal.mul_mem_right _ _ (sig_mem_wc I ha), ?_⟩
    rw [hform_smul_left, ← hb]
    show _ = algebraMap (𝓞 I.E) I.E (sigO I a * b)
    rw [map_mul]
    exact congrArg₂ (· * ·) (sigO_coe I a).symm rfl
  | zero =>
    exact ⟨0, Ideal.zero_mem _, by rw [hform_zero_left]; exact (map_zero (algebraMap (𝓞 I.E) I.E)).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, hc1, e1⟩ := hx
    obtain ⟨c2, hc2, e2⟩ := hy
    exact ⟨c1 + c2, Ideal.add_mem _ hc1 hc2, by
      rw [hform_add_left, e1, e2]; exact (map_add (algebraMap (𝓞 I.E) I.E) c1 c2).symm⟩
  | smul r x _ hx =>
    obtain ⟨c, hc, e⟩ := hx
    refine ⟨sigO I r * c, Ideal.mul_mem_left _ _ hc, ?_⟩
    rw [← algebraMap_smul I.E r x, hform_smul_left, e]
    show _ = algebraMap (𝓞 I.E) I.E (sigO I r * c)
    rw [map_mul]
    exact congrArg₂ (· * ·) (sigO_coe I r).symm rfl

/- English proof (translation)
Unfold `wLat0 at hl`. Proceed by induction on `hl using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, y, hy, rfl⟩` from `hz`. Take `⟨b, hb⟩` from `(I.L_dual y).1 hy u hu`.

Use `⟨a * b, Ideal.mul_mem_right _ _ ha, ?_⟩` and prove the remaining obligations. Rewrite using `[hform_smul_right, ← hb]`. Conclude with `(map_mul (algebraMap (𝓞 I.E) I.E) a b).symm`. Consider the case `zero`. Conclude with `⟨0, Ideal.zero_mem _, by rw [hform_zero_right]; exact (map_zero (algebraMap (𝓞 I.E) I.E)).symm⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨c1, hc1, e1⟩` from `hx`. Take `⟨c2, hc2, e2⟩` from `hy`. Conclude with `⟨c1 + c2, Ideal.add_mem _ hc1 hc2, by`. Rewrite using `[hform_add_right, e1, e2]`.

Conclude with `(map_add (algebraMap (𝓞 I.E) I.E) c1 c2).symm⟩`. Consider the case `smul r x _ hx`. Take `⟨c, hc, e⟩` from `hx`. Use `⟨r * c, Ideal.mul_mem_left _ _ hc, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul I.E r x, hform_smul_right, e]`.

Conclude with `(map_mul (algebraMap (𝓞 I.E) I.E) r c).symm`.
-/
theorem hform_wLat0_right {w : HeightOneSpectrum (𝓞 I.E)} {l : Fin I.n → I.E} (hl : l ∈ wLat0 I w)
    {u : Fin I.n → I.E} (hu : u ∈ I.L) : ∃ c ∈ w.asIdeal, Formalism.UG.hform (starRingEnd I.E) I.J u l = (c : I.E) := by
  unfold wLat0 at hl
  induction hl using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hz
    obtain ⟨b, hb⟩ := (I.L_dual y).1 hy u hu
    refine ⟨a * b, Ideal.mul_mem_right _ _ ha, ?_⟩
    rw [hform_smul_right, ← hb]
    exact (map_mul (algebraMap (𝓞 I.E) I.E) a b).symm
  | zero =>
    exact ⟨0, Ideal.zero_mem _, by rw [hform_zero_right]; exact (map_zero (algebraMap (𝓞 I.E) I.E)).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, hc1, e1⟩ := hx
    obtain ⟨c2, hc2, e2⟩ := hy
    exact ⟨c1 + c2, Ideal.add_mem _ hc1 hc2, by
      rw [hform_add_right, e1, e2]; exact (map_add (algebraMap (𝓞 I.E) I.E) c1 c2).symm⟩
  | smul r x _ hx =>
    obtain ⟨c, hc, e⟩ := hx
    refine ⟨r * c, Ideal.mul_mem_left _ _ hc, ?_⟩
    rw [← algebraMap_smul I.E r x, hform_smul_right, e]
    exact (map_mul (algebraMap (𝓞 I.E) I.E) r c).symm

abbrev iE (a : 𝓞 I.E) : I.E ⊗[I.F] Af I.F := Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E)

/- English proof (translation)
Use `show _ ∈ Subring.closure _`. Conclude with `Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)`.
-/
theorem iE_int (a : 𝓞 I.E) : iE I a ∈ IntAf I.F I.E := by
  show _ ∈ Subring.closure _
  exact Subring.subset_closure (Or.inl ⟨⟨(a : I.E), a, rfl⟩, rfl⟩)

/- English proof (translation)
Unfold `hhat`. Conclude with `hform_sub_right _ _ y z z'`.
-/
theorem hhat_sub_right (y z z' : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I y (z - z') = hhat I y z - hhat I y z' := by
  unfold hhat
  exact hform_sub_right _ _ y z z'

/- English proof (translation)
Unfold `hhat`. Conclude with `hform_sub_left _ _ y y' z`.
-/
theorem hhat_sub_left (y y' z : Fin I.n → I.E ⊗[I.F] Af I.F) : hhat I (y - y') z = hhat I y z - hhat I y' z := by
  unfold hhat
  exact hform_sub_left _ _ y y' z

/- English proof (translation)
Unfold `hhat`. Conclude with `hform_unit _ _ (I.fmat x) x.2 y z`.
-/
theorem hhat_fmat (x : I.Gf) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hhat I (I.fmat x *ᵥ y) (I.fmat x *ᵥ z) = hhat I y z := by
  unfold hhat
  exact hform_unit _ _ (I.fmat x) x.2 y z

/- English proof (translation)
Establish `hincl : ∀ e : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F` using `I.F) (Af I.F) e) = Formalism.UG.inclE (F := I.F) (Af I.F) (star e) := by`. Introduce `e`. Use `first`. Consider the case `rfl`. Consider the case `simp [Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]`.

Establish `hInt : ∀ s ∈ IntAf I.F I.E, Formalism.UG.sigR I.cm.sig (Af I.F) s ∈ IntAf I.F I.E`. Establish `hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F))` using `by show Subring.closure _ ≤ _`. Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)`. Rewrite using `[SetLike.mem_coe, Subring.mem_comap]`.

Use `Subring.subset_closure (Or.inl ⟨⟨_, sigO I a, rfl⟩, ?_⟩)` and prove the remaining obligations. Use `first`. Consider the case `rfl`. Consider the case `simp [Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig, sigO_coe]`. Rewrite using `[SetLike.mem_coe, Subring.mem_comap]`.

Use `Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)` and prove the remaining obligations. Simplify using `[Formalism.UG.sigR]`. Conclude with `fun s hs => hle hs`. Establish `hzl : ∀ z : Fin I.n → I.E ⊗[I.F] Af I.F, hhat I 0 z = 0` using `fun z => by simp [hhat, Formalism.UG.hform]`. Establish `hzr : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, hhat I y 0 = 0` using `fun y => by simp [hhat, Formalism.UG.hform]`.

Establish `hal : ∀ y y' z : Fin I.n → I.E ⊗[I.F] Af I.F, hhat I (y + y') z = hhat I y z + hhat I y' z` using `fun y y' z => by simp only [hhat, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`. Establish `har : ∀ y z z' : Fin I.n → I.E ⊗[I.F] Af I.F, hhat I y (z + z') = hhat I y z + hhat I y z'` using `fun y z z' => by simp only [hhat, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Establish `hsl : ∀ (r : IntAf I.F I.E) (y z : Fin I.n → I.E ⊗[I.F] Af I.F), hhat I (r • y) z = Formalism.UG.sigR I.cm.sig (Af I.F) r * hhat I y z`. Introduce `r y z`. Use `show Formalism.UG.hform _ _ ((r : I.E ⊗[I.F] Af I.F) • y) z = _ * Formalism.UG.hform _ _ y z`.

Conclude with `hform_smul_left _ _ _ _ _`. Establish `hsr : ∀ (r : IntAf I.F I.E) (y z : Fin I.n → I.E ⊗[I.F] Af I.F), hhat I y (r • z) = r * hhat I y z`. Introduce `r y z`. Use `show Formalism.UG.hform _ _ y ((r : I.E ⊗[I.F] Af I.F) • z) = _ * Formalism.UG.hform _ _ y z`. Conclude with `hform_smul_right _ _ _ _ _`.

Establish `Q0 : ∃ s ∈ IntAf I.F I.E, iE I β * 0 = iE I t * s` using `⟨0, zero_mem _, by simp⟩`. Establish `Qadd : ∀ a b, (∃ s ∈ IntAf I.F I.E, iE I β * a = iE I t * s) → (∃ s ∈ IntAf I.F I.E, iE I β * b = iE I t * s) → ∃ s ∈ IntAf I.F I.E, iE I β * (a + b) = iE I t * s`. Introduce and unpack `a b ⟨s1, h1, e1⟩ ⟨s2, h2, e2⟩`. Conclude with `⟨s1 + s2, add_mem h1 h2, by rw [mul_add, e1, e2, mul_add]⟩`. Establish `Qmul : ∀ r ∈ IntAf I.F I.E, ∀ a, (∃ s ∈ IntAf I.F I.E, iE I β * a = iE I t * s) → ∃ s ∈ IntAf I.F I.E, iE I β * (r * a) = iE I t * s`.

Introduce and unpack `r hr a ⟨s, hs, e⟩`. Conclude with `⟨r * s, mul_mem hr hs, by rw [mul_left_comm, e, mul_left_comm]⟩`. Establish `Qgen : ∀ x ∈ wLat0 I w, ∀ y ∈ I.L, ∃ s ∈ IntAf I.F I.E, iE I β * hhat I (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (x i)) (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) = iE I t * s := by`. Introduce `x hx y hy`. Take `⟨c, hc, hcv⟩` from `hform_wLat0 I hx hy`.

Take `⟨g, hg⟩` from `hβ c hc`. Establish `e : hhat I (fun i => Formalism.UG.inclE (F` using `I.F) (Af I.F) (x i)) (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) = Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by`. Simplify using `only [hhat, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, hincl, starRingEnd_apply]`. Use `⟨iE I g, iE_int I g, ?_⟩` and prove the remaining obligations. Rewrite using `[e, hcv]`.

Use `show Formalism.UG.inclE (F := I.F) (Af I.F) (β : I.E) * Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) = Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E) * Formalism.UG.inclE (F := I.F) (Af I.F) (g : I.E)`. Rewrite using `[← map_mul (Formalism.UG.inclE (F := I.F) (Af I.F)), ← map_mul (Formalism.UG.inclE (F := I.F) (Af I.F))]`. Establish `h2` using `congrArg (algebraMap (𝓞 I.E) I.E) hg`. Rewrite `h2` using `[map_mul, map_mul]`. Conclude with `congrArg (Formalism.UG.inclE (F := I.F) (Af I.F)) h2`.

Unfold `Lq lamAf at hu`. Unfold `AutInst.Lf lamAf at hv`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨⟨x, hx⟩, rfl⟩` from `hz`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem z' hz'`. Take `⟨⟨y, hy⟩, rfl⟩` from `hz'`. Conclude with `Qgen x hx y hy`. Consider the case `zero => rw [hzr]`.

Conclude with `Q0`. Consider the case `add a b _ _ ha hb => rw [har]`. Conclude with `Qadd _ _ ha hb`. Consider the case `smul r a _ ha => rw [hsr]`. Conclude with `Qmul _ r.2 _ ha`.

Consider the case `zero => rw [hzl]`. Conclude with `Q0`. Consider the case `add a b _ _ ha hb => rw [hal]`. Conclude with `Qadd _ _ ha hb`. Consider the case `smul r a _ ha => rw [hsl]`.

Conclude with `Qmul _ (hInt _ r.2) _ ha`.
-/
theorem hhat_Lq {w : HeightOneSpectrum (𝓞 I.E)} {t β : 𝓞 I.E}
    (hβ : ∀ a ∈ (wc I w).asIdeal, ∃ g, β * a = t * g) {u : Fin I.n → I.E ⊗[I.F] Af I.F} (hu : u ∈ Lq I w)
    {v : Fin I.n → I.E ⊗[I.F] Af I.F} (hv : v ∈ I.Lf) :
    ∃ s ∈ IntAf I.F I.E, iE I β * hhat I u v = iE I t * s := by
  have hincl : ∀ e : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star e) := by
    intro e
    first
      | rfl
      | simp [Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig]
  have hInt : ∀ s ∈ IntAf I.F I.E, Formalism.UG.sigR I.cm.sig (Af I.F) s ∈ IntAf I.F I.E := by
    have hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
      show Subring.closure _ ≤ _
      rw [Subring.closure_le]
      rintro _ (⟨⟨x, a, rfl⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inl ⟨⟨_, sigO I a, rfl⟩, ?_⟩)
        first
          | rfl
          | simp [Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig, sigO_coe]
      · rw [SetLike.mem_coe, Subring.mem_comap]
        refine Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, ?_⟩)
        simp [Formalism.UG.sigR]
    exact fun s hs => hle hs
  have hzl : ∀ z : Fin I.n → I.E ⊗[I.F] Af I.F, hhat I 0 z = 0 := fun z => by simp [hhat, Formalism.UG.hform]
  have hzr : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, hhat I y 0 = 0 := fun y => by simp [hhat, Formalism.UG.hform]
  have hal : ∀ y y' z : Fin I.n → I.E ⊗[I.F] Af I.F, hhat I (y + y') z = hhat I y z + hhat I y' z :=
    fun y y' z => by simp only [hhat, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have har : ∀ y z z' : Fin I.n → I.E ⊗[I.F] Af I.F, hhat I y (z + z') = hhat I y z + hhat I y z' :=
    fun y z z' => by simp only [hhat, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hsl : ∀ (r : IntAf I.F I.E) (y z : Fin I.n → I.E ⊗[I.F] Af I.F),
      hhat I (r • y) z = Formalism.UG.sigR I.cm.sig (Af I.F) r * hhat I y z := by
    intro r y z
    show Formalism.UG.hform _ _ ((r : I.E ⊗[I.F] Af I.F) • y) z = _ * Formalism.UG.hform _ _ y z
    exact hform_smul_left _ _ _ _ _
  have hsr : ∀ (r : IntAf I.F I.E) (y z : Fin I.n → I.E ⊗[I.F] Af I.F),
      hhat I y (r • z) = r * hhat I y z := by
    intro r y z
    show Formalism.UG.hform _ _ y ((r : I.E ⊗[I.F] Af I.F) • z) = _ * Formalism.UG.hform _ _ y z
    exact hform_smul_right _ _ _ _ _
  have Q0 : ∃ s ∈ IntAf I.F I.E, iE I β * 0 = iE I t * s := ⟨0, zero_mem _, by simp⟩
  have Qadd : ∀ a b, (∃ s ∈ IntAf I.F I.E, iE I β * a = iE I t * s) →
      (∃ s ∈ IntAf I.F I.E, iE I β * b = iE I t * s) → ∃ s ∈ IntAf I.F I.E, iE I β * (a + b) = iE I t * s := by
    rintro a b ⟨s1, h1, e1⟩ ⟨s2, h2, e2⟩
    exact ⟨s1 + s2, add_mem h1 h2, by rw [mul_add, e1, e2, mul_add]⟩
  have Qmul : ∀ r ∈ IntAf I.F I.E, ∀ a, (∃ s ∈ IntAf I.F I.E, iE I β * a = iE I t * s) →
      ∃ s ∈ IntAf I.F I.E, iE I β * (r * a) = iE I t * s := by
    rintro r hr a ⟨s, hs, e⟩
    exact ⟨r * s, mul_mem hr hs, by rw [mul_left_comm, e, mul_left_comm]⟩
  have Qgen : ∀ x ∈ wLat0 I w, ∀ y ∈ I.L, ∃ s ∈ IntAf I.F I.E,
      iE I β * hhat I (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i))
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) = iE I t * s := by
    intro x hx y hy
    obtain ⟨c, hc, hcv⟩ := hform_wLat0 I hx hy
    obtain ⟨g, hg⟩ := hβ c hc
    have e : hhat I (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i))
        (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) =
        Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
      simp only [hhat, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, hincl, starRingEnd_apply]
    refine ⟨iE I g, iE_int I g, ?_⟩
    rw [e, hcv]
    show Formalism.UG.inclE (F := I.F) (Af I.F) (β : I.E) * Formalism.UG.inclE (F := I.F) (Af I.F) (c : I.E) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (t : I.E) * Formalism.UG.inclE (F := I.F) (Af I.F) (g : I.E)
    rw [← map_mul (Formalism.UG.inclE (F := I.F) (Af I.F)), ← map_mul (Formalism.UG.inclE (F := I.F) (Af I.F))]
    have h2 := congrArg (algebraMap (𝓞 I.E) I.E) hg
    rw [map_mul, map_mul] at h2
    exact congrArg (Formalism.UG.inclE (F := I.F) (Af I.F)) h2
  unfold Lq lamAf at hu
  unfold AutInst.Lf lamAf at hv
  induction hu using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨x, hx⟩, rfl⟩ := hz
    induction hv using Submodule.span_induction with
    | mem z' hz' =>
      obtain ⟨⟨y, hy⟩, rfl⟩ := hz'
      exact Qgen x hx y hy
    | zero => rw [hzr]; exact Q0
    | add a b _ _ ha hb => rw [har]; exact Qadd _ _ ha hb
    | smul r a _ ha => rw [hsr]; exact Qmul _ r.2 _ ha
  | zero => rw [hzl]; exact Q0
  | add a b _ _ ha hb => rw [hal]; exact Qadd _ _ ha hb
  | smul r a _ ha => rw [hsl]; exact Qmul _ (hInt _ r.2) _ ha

/- English proof (translation)
Take `⟨t, β, htw, ht0, hβ, hβw⟩` from `exists_ideal_element_not_mem I (wc I w)`. Introduce `y hy`. Use `set z := (I.fmat x - 1) *ᵥ y with hz_def`. Establish `hz : z ∈ I.Lf` using `K_sub_mv I hx hy`. Establish `hxi : x⁻¹ ∈ I.Kset` using `K_inv I hx`.

Establish `hsw : ∀ u ∈ I.Lf, hhat I u z = hhat I ((I.fmat x⁻¹ - 1) *ᵥ u) y`. Introduce `u _`. Establish `e1 : hhat I u (I.fmat x *ᵥ y) = hhat I (I.fmat x⁻¹ *ᵥ u) y` using `by conv_lhs => rw [show u = I.fmat x *ᵥ (I.fmat x⁻¹ *ᵥ u) by`. Rewrite using `[Matrix.mulVec_mulVec, DictGen.fmat_mul_inv, Matrix.one_mulVec]]`. Conclude with `hhat_fmat I x _ _`.

Rewrite using `[hz_def, Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_right, e1, Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_left]`. Establish `hmem : ∀ u ∈ I.Lf, (I.fmat x⁻¹ - 1) *ᵥ u ∈ Lq I w`. Introduce `u hu`. Establish `e : (I.fmat x⁻¹ - 1) *ᵥ u = -(I.fmat x⁻¹ *ᵥ ((I.fmat x - 1) *ᵥ u))`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_sub, DictGen.fmat_inv_mul, Matrix.mul_one, Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `neg_mem (stab_w I w hxi (hA u hu))`. Establish `hint : ∀ u ∈ I.Lf, ∃ s ∈ IntAf I.F I.E, iE I β * hhat I u z = iE I t * s`. Introduce `u hu`.

Rewrite using `[hsw u hu]`. Conclude with `hhat_Lq I hβ (hmem u hu) hy`. Establish `htE : ((t : 𝓞 I.E) : I.E) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.2 ht0`. Use `set c : I.E ⊗[I.F] Af I.F := Formalism.UG.inclE (F := I.F) (Af I.F) (((t : 𝓞 I.E) : I.E)⁻¹)`. Establish `hct : c * iE I t = 1`.

Simplify using `only [c, iE, ← map_mul, inv_mul_cancel₀ htE, map_one]`. Establish `hz' : c • (iE I β • z) ∈ I.Lf`. Use `dual_hat_lattice I _ fun u hu => ?_` and prove the remaining obligations. Take `⟨s, hs, e⟩` from `hint u hu`. Rewrite using `[DictLat.hhat_smul_right, DictLat.hhat_smul_right, e, ← mul_assoc, hct, one_mul]`.

Conclude with `hs`. Establish `hβz : iE I β • z ∈ Lq I (wc I w)`. Establish `e : iE I β • z = iE I t • (c • (iE I β • z))`. Rewrite using `[smul_smul, mul_comm, hct, one_smul]`. Rewrite using `[e]`.

Conclude with `smul_mem I (wc I w) htw hz'`. Take `⟨γ, i, hi, hγ⟩` from `Ideal.IsMaximal.exists_inv (inferInstance : (wc I w).asIdeal.IsMaximal) hβw`. Establish `hγ' : iE I γ * iE I β + iE I i = 1`. Use `congrArg (fun a : 𝓞 I.E => Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E)) hγ` as an intermediate fact. Simplify `this` using `[iE, map_add, map_mul]`.

Establish `e2 : z = iE I γ • (iE I β • z) + iE I i • z`. Rewrite using `[smul_smul, ← add_smul, hγ', one_smul]`. Rewrite using `[e2]`. Conclude with `add_mem ((Lq I (wc I w)).smul_mem ⟨iE I γ, iE_int I γ⟩ hβz) (smul_mem I (wc I w) hi hz)`.
-/
theorem stepB {w : HeightOneSpectrum (𝓞 I.E)} {x : I.Gf} (hx : x ∈ I.Kset)
    (hA : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ Lq I w) : ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ Lq I (wc I w) := by
  obtain ⟨t, β, htw, ht0, hβ, hβw⟩ := exists_ideal_element_not_mem I (wc I w)
  intro y hy
  set z := (I.fmat x - 1) *ᵥ y with hz_def
  have hz : z ∈ I.Lf := K_sub_mv I hx hy
  have hxi : x⁻¹ ∈ I.Kset := K_inv I hx

  have hsw : ∀ u ∈ I.Lf, hhat I u z = hhat I ((I.fmat x⁻¹ - 1) *ᵥ u) y := by
    intro u _
    have e1 : hhat I u (I.fmat x *ᵥ y) = hhat I (I.fmat x⁻¹ *ᵥ u) y := by
      conv_lhs => rw [show u = I.fmat x *ᵥ (I.fmat x⁻¹ *ᵥ u) by
        rw [Matrix.mulVec_mulVec, DictGen.fmat_mul_inv, Matrix.one_mulVec]]
      exact hhat_fmat I x _ _
    rw [hz_def, Matrix.sub_mulVec, Matrix.one_mulVec, hhat_sub_right, e1, Matrix.sub_mulVec, Matrix.one_mulVec,
      hhat_sub_left]
  have hmem : ∀ u ∈ I.Lf, (I.fmat x⁻¹ - 1) *ᵥ u ∈ Lq I w := by
    intro u hu
    have e : (I.fmat x⁻¹ - 1) *ᵥ u = -(I.fmat x⁻¹ *ᵥ ((I.fmat x - 1) *ᵥ u)) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_sub, DictGen.fmat_inv_mul, Matrix.mul_one, Matrix.sub_mulVec,
        Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [e]
    exact neg_mem (stab_w I w hxi (hA u hu))
  have hint : ∀ u ∈ I.Lf, ∃ s ∈ IntAf I.F I.E, iE I β * hhat I u z = iE I t * s := by
    intro u hu
    rw [hsw u hu]
    exact hhat_Lq I hβ (hmem u hu) hy
  have htE : ((t : 𝓞 I.E) : I.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ht0
  set c : I.E ⊗[I.F] Af I.F := Formalism.UG.inclE (F := I.F) (Af I.F) (((t : 𝓞 I.E) : I.E)⁻¹)
  have hct : c * iE I t = 1 := by
    simp only [c, iE, ← map_mul, inv_mul_cancel₀ htE, map_one]
  have hz' : c • (iE I β • z) ∈ I.Lf := by
    refine dual_hat_lattice I _ fun u hu => ?_
    obtain ⟨s, hs, e⟩ := hint u hu
    rw [DictLat.hhat_smul_right, DictLat.hhat_smul_right, e, ← mul_assoc, hct, one_mul]
    exact hs
  have hβz : iE I β • z ∈ Lq I (wc I w) := by
    have e : iE I β • z = iE I t • (c • (iE I β • z)) := by
      rw [smul_smul, mul_comm, hct, one_smul]
    rw [e]
    exact smul_mem I (wc I w) htw hz'
  obtain ⟨γ, i, hi, hγ⟩ := Ideal.IsMaximal.exists_inv (inferInstance : (wc I w).asIdeal.IsMaximal) hβw
  have hγ' : iE I γ * iE I β + iE I i = 1 := by
    have := congrArg (fun a : 𝓞 I.E => Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E)) hγ
    simpa [iE, map_add, map_mul] using this
  have e2 : z = iE I γ • (iE I β • z) + iE I i • z := by
    rw [smul_smul, ← add_smul, hγ', one_smul]
  rw [e2]
  exact add_mem ((Lq I (wc I w)).smul_mem ⟨iE I γ, iE_int I γ⟩ hβz) (smul_mem I (wc I w) hi hz)

/- English proof (translation)
Distinguish the cases in `ha0 : a = 0`. Rewrite using `[ha0]`. Conclude with `Ideal.zero_mem _`. Establish `hp0 : ((p : ℕ) : 𝓞 E) ≠ 0` using `fun h => hp.ne_zero (by`. Establish `h'` using `congrArg (algebraMap (𝓞 E) E) h`.

Simplify using `using h')`. Establish `hI : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hp0`. Establish `hJ : Ideal.span {a} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `ha0`. Establish `hdvd : Ideal.span {((p : ℕ) : 𝓞 E)} ∣ Ideal.span {a}`. Rewrite using `[UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI hJ, Multiset.le_iff_count]`. Introduce `P`.

Distinguish the cases in `hP : P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})`. Rewrite `hP` using `[Ideal.mem_normalizedFactors_iff hI]`. Take `⟨hPp, hle⟩` from `hP`. Establish `hpP : ((p : ℕ) : 𝓞 E) ∈ P` using `hle (Ideal.mem_span_singleton_self _)`. Establish `hP0 : P ≠ ⊥` using `fun h => hp0 (by rw [h] at hpP; exact (Submodule.mem_bot _).1 hpP)`.

Establish `hmax : P.IsMaximal` using `hPp.isMaximal hP0`. Use `haveI := hPp`. Establish `h1 : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).count P = 1`. Apply `Ideal.count_normalizedFactors_eq` to reduce the goal to its premises. Rewrite using `[pow_one]`.

Conclude with `hle`. Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `hun P hmax hpP`. Rewrite using `[h1, Multiset.one_le_count_iff_mem, Ideal.mem_normalizedFactors_iff hJ]`. Conclude with `⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 (ha P hmax hpP)⟩`.

Rewrite using `[Multiset.count_eq_zero.2 hP]`. Conclude with `Nat.zero_le _`. Conclude with `(Ideal.dvd_iff_le.1 hdvd) (Ideal.mem_span_singleton_self a)`.
-/
theorem mem_span_of_all {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (hun : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → (p : 𝓞 E) ∉ P ^ 2) {a : 𝓞 E}
    (ha : ∀ P : Ideal (𝓞 E), P.IsMaximal → (p : 𝓞 E) ∈ P → a ∈ P) : a ∈ Ideal.span {((p : ℕ) : 𝓞 E)} := by
  classical
  by_cases ha0 : a = 0
  · rw [ha0]
    exact Ideal.zero_mem _
  have hp0 : ((p : ℕ) : 𝓞 E) ≠ 0 := fun h => hp.ne_zero (by
    have h' := congrArg (algebraMap (𝓞 E) E) h
    simpa using h')
  have hI : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hp0
  have hJ : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha0
  have hdvd : Ideal.span {((p : ℕ) : 𝓞 E)} ∣ Ideal.span {a} := by
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hI hJ, Multiset.le_iff_count]
    intro P
    by_cases hP : P ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})
    · rw [Ideal.mem_normalizedFactors_iff hI] at hP
      obtain ⟨hPp, hle⟩ := hP
      have hpP : ((p : ℕ) : 𝓞 E) ∈ P := hle (Ideal.mem_span_singleton_self _)
      have hP0 : P ≠ ⊥ := fun h => hp0 (by rw [h] at hpP; exact (Submodule.mem_bot _).1 hpP)
      have hmax : P.IsMaximal := hPp.isMaximal hP0
      haveI := hPp
      have h1 : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((p : ℕ) : 𝓞 E)})).count P = 1 := by
        apply Ideal.count_normalizedFactors_eq
        · rw [pow_one]
          exact hle
        · rw [Ideal.span_singleton_le_iff_mem]
          exact hun P hmax hpP
      rw [h1, Multiset.one_le_count_iff_mem, Ideal.mem_normalizedFactors_iff hJ]
      exact ⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 (ha P hmax hpP)⟩
    · rw [Multiset.count_eq_zero.2 hP]
      exact Nat.zero_le _
  exact (Ideal.dvd_iff_le.1 hdvd) (Ideal.mem_span_singleton_self a)

/- English proof (translation)
Use `⟨hx, fun y hy => ?_⟩` and prove the remaining obligations. Establish `hz : (I.fmat x - 1) *ᵥ y ∈ I.Lf` using `K_sub_mv I hx hy`. Take `⟨l, hl, z', hz', he⟩` from `lattice_dense I p hp.pos _ hz`. Establish `hpE : (p : I.E ⊗[I.F] Af I.F) = Formalism.UG.inclE (F` using `I.F) (Af I.F) (((p : 𝓞 I.E)) : I.E) := by simp`. Establish `hlw : ∀ w : HeightOneSpectrum (𝓞 I.E), (p : 𝓞 I.E) ∈ w.asIdeal → l ∈ wLat0 I w`.

Introduce `w hw`. Use `inter I w ?_` and prove the remaining obligations. Establish `e : iv I l = (I.fmat x - 1) *ᵥ y - (p : I.E ⊗[I.F] Af I.F) • z'` using `by rw [he]; abel`. Rewrite using `[e]`. Use `sub_mem (h w hw y hy) ?_` and prove the remaining obligations.

Rewrite using `[hpE]`. Conclude with `smul_mem I w hw hz'`. Establish `hdiv : ∀ u ∈ I.L, ∃ o : 𝓞 I.E, Formalism.UG.hform (starRingEnd I.E) I.J u l = ((p * o : 𝓞 I.E) : I.E)`. Introduce `u hu`. Take `⟨o, ho⟩` from `(I.L_dual l).1 hl u hu`.

Establish `hall : ∀ P : Ideal (𝓞 I.E), P.IsMaximal → (p : 𝓞 I.E) ∈ P → o ∈ P`. Introduce `P hPm hpP`. Set `w : HeightOneSpectrum (𝓞 I.E)` to `⟨P, hPm.isPrime, fun hb => by`. Rewrite `hpP` using `[hb]`. Conclude with `(by exact_mod_cast hp.ne_zero : ((p : ℕ) : 𝓞 I.E) ≠ 0) ((Submodule.mem_bot _).1 hpP)⟩`.

Take `⟨c, hc, e⟩` from `hform_wLat0_right I (hlw w hpP) hu`. Establish `: o = c` using `RingOfIntegers.ext (by rw [← e]; exact ho)`. Rewrite using `[this]`. Conclude with `hc`. Take `⟨o', ho'⟩` from `Ideal.mem_span_singleton'.1 (mem_span_of_all hp hun hall)`.

Conclude with `⟨o', by rw [← ho, ← ho', mul_comm]⟩`. Establish `hpE0 : ((p : ℕ) : I.E) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Use `set l' : Fin I.n → I.E := ((p : I.E))⁻¹ • l`. Establish `hl' : l' ∈ I.L`. Use `(I.L_dual l').2 fun u hu => ?_` and prove the remaining obligations.

Take `⟨o', ho'⟩` from `hdiv u hu`. Use `⟨o', ?_⟩` and prove the remaining obligations. Rewrite using `[hform_smul_right, ho']`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `hll : l = (p : I.E) • l'` using `by simp only [l', smul_smul, mul_inv_cancel₀ hpE0, one_smul]`. Use `⟨iv I l' + z', add_mem (DictLat.iv_mem I hl') hz', ?_⟩` and prove the remaining obligations. Rewrite using `[he, hll, DictLat.iv_smulE, smul_add]`. Use `congr 1`.
-/
theorem glue {p : ℕ} (hp : p.Prime)
    (hun : ∀ P : Ideal (𝓞 I.E), P.IsMaximal → (p : 𝓞 I.E) ∈ P → (p : 𝓞 I.E) ∉ P ^ 2) {x : I.Gf}
    (hx : x ∈ I.Kset)
    (h : ∀ w : HeightOneSpectrum (𝓞 I.E), (p : 𝓞 I.E) ∈ w.asIdeal → ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ Lq I w) :
    x ∈ I.Kg p := by
  refine ⟨hx, fun y hy => ?_⟩
  have hz : (I.fmat x - 1) *ᵥ y ∈ I.Lf := K_sub_mv I hx hy
  obtain ⟨l, hl, z', hz', he⟩ := lattice_dense I p hp.pos _ hz
  have hpE : (p : I.E ⊗[I.F] Af I.F) = Formalism.UG.inclE (F := I.F) (Af I.F) (((p : 𝓞 I.E)) : I.E) := by simp
  have hlw : ∀ w : HeightOneSpectrum (𝓞 I.E), (p : 𝓞 I.E) ∈ w.asIdeal → l ∈ wLat0 I w := by
    intro w hw
    refine inter I w ?_
    have e : iv I l = (I.fmat x - 1) *ᵥ y - (p : I.E ⊗[I.F] Af I.F) • z' := by rw [he]; abel
    rw [e]
    refine sub_mem (h w hw y hy) ?_
    rw [hpE]
    exact smul_mem I w hw hz'
  have hdiv : ∀ u ∈ I.L, ∃ o : 𝓞 I.E, Formalism.UG.hform (starRingEnd I.E) I.J u l = ((p * o : 𝓞 I.E) : I.E) := by
    intro u hu
    obtain ⟨o, ho⟩ := (I.L_dual l).1 hl u hu
    have hall : ∀ P : Ideal (𝓞 I.E), P.IsMaximal → (p : 𝓞 I.E) ∈ P → o ∈ P := by
      intro P hPm hpP
      let w : HeightOneSpectrum (𝓞 I.E) := ⟨P, hPm.isPrime, fun hb => by
        rw [hb] at hpP
        exact (by exact_mod_cast hp.ne_zero : ((p : ℕ) : 𝓞 I.E) ≠ 0) ((Submodule.mem_bot _).1 hpP)⟩
      obtain ⟨c, hc, e⟩ := hform_wLat0_right I (hlw w hpP) hu
      have : o = c := RingOfIntegers.ext (by rw [← e]; exact ho)
      rw [this]; exact hc
    obtain ⟨o', ho'⟩ := Ideal.mem_span_singleton'.1 (mem_span_of_all hp hun hall)
    exact ⟨o', by rw [← ho, ← ho', mul_comm]⟩
  have hpE0 : ((p : ℕ) : I.E) ≠ 0 := by exact_mod_cast hp.ne_zero
  set l' : Fin I.n → I.E := ((p : I.E))⁻¹ • l
  have hl' : l' ∈ I.L := by
    refine (I.L_dual l').2 fun u hu => ?_
    obtain ⟨o', ho'⟩ := hdiv u hu
    refine ⟨o', ?_⟩
    rw [hform_smul_right, ho']
    push_cast
    field_simp
  have hll : l = (p : I.E) • l' := by simp only [l', smul_smul, mul_inv_cancel₀ hpE0, one_smul]
  refine ⟨iv I l' + z', add_mem (DictLat.iv_mem I hl') hz', ?_⟩
  rw [he, hll, DictLat.iv_smulE, smul_add]
  congr 1

end Formalism.L2.SG.Pf.AllRowsRedKerA
