import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevE
import Formalism.LocalRingCardinality.SpanPowerMembership.NZLevA
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ClsLat
import Formalism.LocalToGlobal.GroupLattices.FockModels.OperatorsPreserveLattices

open MvPolynomial

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.G.Model

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  [CharZero Kf] (P : Places p O Kf)

def L0 : ∀ v, Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) :=
  fun v => colSpan (P.W v) (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))

/- English proof (translation)
The claim follows from `Formalism.L2.G.Cmp.mem_stdL R x`.
-/
theorem mem_colSpan_one {R K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (x : Fin k → K) :
    x ∈ colSpan R (1 : Matrix (Fin k) (Fin k) K) ↔ ∀ a, x a ∈ (algebraMap R K).range :=
  Formalism.L2.G.Cmp.mem_stdL R x

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => exact ⟨x, rfl⟩`. Consider the case `succ n ih`. Take `⟨y, hy⟩` from `ih x`. Take `⟨z, hz⟩` from `(P.setting v).frob y`.

Use `⟨y ^ p + (p : P.W v) * z, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ']`. Use `show (P.σ v) (((P.σ v) ^ n) (algebraMap (P.W v) (P.Qq v) x)) = _`. Rewrite using `[hy, hz]`.
-/
theorem sigma_pow_int (v : Fin P.nV) (n : ℕ) (x : P.W v) :
    ∃ y : P.W v, ((P.σ v) ^ n) (algebraMap (P.W v) (P.Qq v) x) = algebraMap (P.W v) (P.Qq v) y := by
  induction n generalizing x with
  | zero => exact ⟨x, rfl⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih x
    obtain ⟨z, hz⟩ := (P.setting v).frob y
    refine ⟨y ^ p + (p : P.W v) * z, ?_⟩
    rw [pow_succ']
    show (P.σ v) (((P.σ v) ^ n) (algebraMap (P.W v) (P.Qq v) x)) = _
    rw [hy, hz]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Unfold `extO`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Rewrite using `[SetLike.mem_coe, mem_colSpan_one]`.

Introduce `a`. Take `⟨x, hx⟩` from `(mem_colSpan_one y).mp hy a`. Take `⟨z, hz⟩` from `sigma_pow_int P v s x`. Use `⟨(P.j v) z, ?_⟩` and prove the remaining obligations. Rewrite using `[twistVec, ← hx, hz, (P.setting v).ι_comp]`.

Unfold `colSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Rewrite using `[SetLike.mem_coe]`. Establish `h2 : twistVec (P.ι v) (P.σ v) s (fun i => (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) i c) ∈ extO O (P.ι v) (P.σ v) s (L0 P v)` using `Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, rfl⟩, rfl⟩`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `only [twistVec, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem extension_standardLattice (v : Fin P.nV) (s : ℕ) :
    extO O (P.ι v) (P.σ v) s (L0 P v) = colSpan O (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) := by
  apply le_antisymm
  · unfold extO
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_colSpan_one]
    intro a
    obtain ⟨x, hx⟩ := (mem_colSpan_one y).mp hy a
    obtain ⟨z, hz⟩ := sigma_pow_int P v s x
    refine ⟨(P.j v) z, ?_⟩
    rw [twistVec, ← hx, hz, (P.setting v).ι_comp]
  · unfold colSpan
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe]
    have h2 : twistVec (P.ι v) (P.σ v) s (fun i => (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) i c) ∈
        extO O (P.ι v) (P.σ v) s (L0 P v) :=
      Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, rfl⟩, rfl⟩
    convert h2 using 1
    funext i
    simp only [twistVec, Matrix.one_apply]
    split_ifs <;> simp

def intP : Subring P.Xsp := (MvPolynomial.map (algebraMap O Kf)).range

/- English proof (translation)
Take `⟨g, rfl⟩` from `hf`. Conclude with `⟨o • g, by rw [map_smul', algebraMap_smul]⟩`.
-/
theorem intP_smul (o : O) {f : P.Xsp} (hf : f ∈ intP P) : o • f ∈ intP P := by
  obtain ⟨g, rfl⟩ := hf
  exact ⟨o • g, by rw [map_smul', algebraMap_smul]⟩

/- English proof (translation)
Unfold `Dl0 at hf`. Rewrite `hf` using `[if_pos (lamAt_antitone' _ (P.dom v) s)]`. Simplify using `only [Submodule.mem_iInf] at hf`. Establish `h1` using `hf 1 ⟨by simp, extension_standardLattice P v s.val⟩`. Take `⟨x, hx, rfl⟩` from `h1`.

Take `⟨w0, -, hw0⟩` from `hx`. Use `⟨w0, ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.det_one, one_zpow, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, one_smul]`. Establish `: rowAct Kf (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) x = x` using `by rw [rowAct_one']; rfl`. Rewrite using `[← this]`.

Conclude with `hw0`.
-/
theorem Dl0_int (v : Fin P.nV) (s : Fin (P.n' v)) (f : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) Kf)
    (hf : f ∈ Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L0 P v))) :
    ∃ g : MvPolynomial (Fin (P.m + 1) × Fin (P.m + 1)) O, MvPolynomial.map (algebraMap O Kf) g = f := by
  unfold Dl0 at hf
  rw [if_pos (lamAt_antitone' _ (P.dom v) s)] at hf
  simp only [Submodule.mem_iInf] at hf
  have h1 := hf 1 ⟨by simp, extension_standardLattice P v s.val⟩
  obtain ⟨x, hx, rfl⟩ := h1
  obtain ⟨w0, -, hw0⟩ := hx
  refine ⟨w0, ?_⟩
  simp only [Matrix.det_one, one_zpow, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, one_smul]
  have : rowAct Kf (1 : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) x = x := by rw [rowAct_one']; rfl
  rw [← this]
  exact hw0

/- English proof (translation)
Unfold `HtenW tensorLat at hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨G, hG, rfl⟩` from `hy`. Rewrite using `[map_prod]`.

Use `Subring.prod_mem _ fun s _ => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `Dl0_int P v s (G s) (hG s)`. Use `⟨rename (fun y => (⟨v, (s, y)⟩ : Σ v : Fin P.nV, Fin (P.n' v) × _)) g, ?_⟩` and prove the remaining obligations. Rewrite using `[map_rename, hg]`. Unfold `Places.vEmb blockEmb`.

Rewrite using `[rename_rename]`. Both sides reduce to the same expression. Consider the case `zero => rw [map_zero]`. Conclude with `Subring.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `Subring.add_mem _ ha hb`. Consider the case `smul o a _ ha`. Rewrite using `[← algebraMap_smul Kf o a, map_smul, algebraMap_smul]`. Conclude with `intP_smul P o ha`.
-/
theorem htenW_int (v : Fin P.nV) (y : MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)
    (hy : y ∈ HtenW O (P.lam0 v) fun s => extO O (P.ι v) (P.σ v) s.val (L0 P v)) : P.vEmb v y ∈ intP P := by
  unfold HtenW tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨G, hG, rfl⟩ := hy
    rw [map_prod]
    refine Subring.prod_mem _ fun s _ => ?_
    obtain ⟨g, hg⟩ := Dl0_int P v s (G s) (hG s)
    refine ⟨rename (fun y => (⟨v, (s, y)⟩ : Σ v : Fin P.nV, Fin (P.n' v) × _)) g, ?_⟩
    rw [map_rename, hg]
    unfold Places.vEmb blockEmb
    rw [rename_rename]; rfl
  | zero => rw [map_zero]; exact Subring.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Subring.add_mem _ ha hb
  | smul o a _ ha =>
    rw [← algebraMap_smul Kf o a, map_smul, algebraMap_smul]
    exact intP_smul P o ha

/- English proof (translation)
Unfold `Places.HtupW Places.tenV at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨F, hF, rfl⟩` from `hx`. Conclude with `Subring.prod_mem _ fun v _ => htenW_int P v (F v) (hF v)`.

Consider the case `zero => exact Subring.zero_mem _`. Consider the case `add a b _ _ ha hb => exact Subring.add_mem _ ha hb`. Consider the case `smul o a _ ha => exact intP_smul P o ha`.
-/
theorem htupW_int (f : P.Xsp) (hf : f ∈ P.HtupW (L0 P)) : f ∈ intP P := by
  unfold Places.HtupW Places.tenV at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact Subring.prod_mem _ fun v _ => htenW_int P v (F v) (hF v)
  | zero => exact Subring.zero_mem _
  | add a b _ _ ha hb => exact Subring.add_mem _ ha hb
  | smul o a _ ha => exact intP_smul P o ha

def idPt : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) → Kf :=
  fun x => if x.2.2.1 = x.2.2.2 then 1 else 0

/- English proof (translation)
Take `⟨g, rfl⟩` from `hf`. Establish `key : (eval (idPt P)).comp (MvPolynomial.map (algebraMap O Kf)) = (algebraMap O Kf).comp (eval fun x : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) => if x.2.2.1 = x.2.2.2 then (1 : O) else 0)`. Use `MvPolynomial.ringHom_ext (fun a => by simp) (fun x => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, map_X, eval_X, idPt]`. Apply the tactic sequence `split_ifs <;> simp`.

Conclude with `⟨_, (RingHom.congr_fun key g).symm⟩`.
-/
theorem eval_int (f : P.Xsp) (hf : f ∈ intP P) : eval (idPt P) f ∈ (algebraMap O Kf).range := by
  obtain ⟨g, rfl⟩ := hf
  have key : (eval (idPt P)).comp (MvPolynomial.map (algebraMap O Kf)) =
      (algebraMap O Kf).comp (eval fun x : (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) =>
        if x.2.2.1 = x.2.2.2 then (1 : O) else 0) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp) (fun x => ?_)
    simp only [RingHom.comp_apply, map_X, eval_X, idPt]
    split_ifs <;> simp
  exact ⟨_, (RingHom.congr_fun key g).symm⟩

/- English proof (translation)
Unfold `EV prodF`. Rewrite using `[map_prod]`. Use `Finset.prod_eq_one fun v _ => ?_` and prove the remaining obligations. Unfold `Places.vEmb`. Rewrite using `[eval_rename, map_prod]`.

Use `Finset.prod_eq_one fun s _ => ?_` and prove the remaining obligations. Unfold `blockEmb`. Rewrite using `[eval_rename]`. Use `sw_eval_hw Kf le_rfl (nuV P v s) using 2` and compare the differences between its conclusion and the goal. Use `congr 1`.

Use function extensionality and compare the values at `y`. Simplify using `[idPt, Formalism.GradedWeylDivisibility.idPoint, Fin.ext_iff]`.
-/
theorem eval_EV : eval (idPt P) (EV P) = 1 := by
  unfold EV prodF
  rw [map_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  unfold Places.vEmb
  rw [eval_rename, map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  unfold blockEmb
  rw [eval_rename]
  convert sw_eval_hw Kf le_rfl (nuV P v s) using 2
  congr 1
  funext y
  simp [idPt, Formalism.GradedWeylDivisibility.idPoint, Fin.ext_iff]

/- English proof (translation)
Introduce `h`. Use `eval_EV P` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`.
-/
theorem EV_ne : EV P ≠ 0 := by
  intro h
  have := eval_EV P
  rw [h, map_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Unfold `hw lpMinor`. Simplify using `only [map_prod, map_pow, RingHom.map_det]`. Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `congr 2`. Use extensionality with `a b`.

Simplify using `[RingHom.mapMatrix_apply, map_X]`.
-/
theorem hw_map (ν : Fin (P.m + 1) → ℕ) :
    MvPolynomial.map (algebraMap O Kf) (hw O le_rfl ν) = hw Kf le_rfl ν := by
  unfold hw lpMinor
  simp only [map_prod, map_pow, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => ?_
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply, map_X]

/- English proof (translation)
Unfold `Places.HtupW Places.tenV EV prodF`. Use `Submodule.subset_span ⟨fun v => ∏ s, blockEmb Kf s (hw Kf le_rfl (nuV P v s)), fun v => ?_, rfl⟩` and prove the remaining obligations. Unfold `HtenW tensorLat`. Use `Submodule.subset_span ⟨fun s => hw Kf le_rfl (nuV P v s), fun s => ?_, rfl⟩` and prove the remaining obligations. Use `show hw Kf le_rfl (nuV P v s) ∈ Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L0 P v))`.

Unfold `Dl0`. Rewrite using `[if_pos (lamAt_antitone' _ (P.dom v) s)]`. Simplify using `only [Submodule.mem_iInf]`. Introduce and unpack `g ⟨hg, hgΛ⟩`. Establish `hinj : Function.Injective (algebraMap O Kf)` using `@IsFractionRing.injective O _ Kf _ _ (P.setting v).frac_O`.

Use `dl_indep hinj P.m _ 1 g (by simp) ((extension_standardLattice P v s.val).symm.trans hgΛ) ?_` and prove the remaining obligations. Use `⟨hw Kf le_rfl (nuV P v s), ⟨hw O le_rfl (nuV P v s), Submodule.subset_span ⟨[], rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show MvPolynomial.map (algebraMap O Kf) _ = rowAct Kf 1 _`. Rewrite using `[rowAct_one']`. Conclude with `hw_map P _`.

Simplify using the standard rewrite rules.
-/
theorem EV_mem : EV P ∈ P.HtupW (L0 P) := by
  unfold Places.HtupW Places.tenV EV prodF
  refine Submodule.subset_span ⟨fun v => ∏ s, blockEmb Kf s (hw Kf le_rfl (nuV P v s)), fun v => ?_, rfl⟩
  unfold HtenW tensorLat
  refine Submodule.subset_span ⟨fun s => hw Kf le_rfl (nuV P v s), fun s => ?_, rfl⟩
  show hw Kf le_rfl (nuV P v s) ∈ Dl0 O P.m (lamAt (P.lam0 v) s) (extO O (P.ι v) (P.σ v) s.val (L0 P v))
  unfold Dl0
  rw [if_pos (lamAt_antitone' _ (P.dom v) s)]
  simp only [Submodule.mem_iInf]
  rintro g ⟨hg, hgΛ⟩
  have hinj : Function.Injective (algebraMap O Kf) := @IsFractionRing.injective O _ Kf _ _ (P.setting v).frac_O
  refine dl_indep hinj P.m _ 1 g (by simp) ((extension_standardLattice P v s.val).symm.trans hgΛ) ?_
  refine ⟨hw Kf le_rfl (nuV P v s), ⟨hw O le_rfl (nuV P v s), Submodule.subset_span ⟨[], rfl⟩, ?_⟩, ?_⟩
  · show MvPolynomial.map (algebraMap O Kf) _ = rowAct Kf 1 _
    rw [rowAct_one']; exact hw_map P _
  · simp

end Formalism.BasicNotions.Examples₂.NZ
