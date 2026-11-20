import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.WittCompl

/- English proof (translation)
Simplify using `only [Module.Basis.equivFun_symm_apply]`. Simplify using `only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, HSpace.gram, starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_coords {D : D7} (V : HSp D) (a b : Fin V.rank → D.host.E) :
    V.hT (V.frame.equivFun.symm a) (V.frame.equivFun.symm b) =
      ∑ k, ∑ l, star (a k) * V.gram k l * b l := by
  simp only [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, HSpace.gram,
    starRingEnd_apply, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Rewrite using `[hT_coords]`. Simplify using `only [Matrix.mul_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.
-/
theorem hT_cols {D : D7} (V : HSp D) {m : ℕ} (A B : Matrix (Fin V.rank) (Fin m) D.host.E) (i j : Fin m) :
    V.hT (V.frame.equivFun.symm fun k => A k i) (V.frame.equivFun.symm fun k => B k j) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A * V.gram * B) i j := by
  rw [hT_coords]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

/- English proof (translation)
Establish `hs` using `V.herm`. Establish `hdc : ∀ i j, V.hT (d i) (c j) = if i = j then 1 else 0` using `fun i j => by`. Rewrite using `[← hs.eq (c j) (d i), hcd]`. Distinguish the cases in `h : i = j`. Simplify using `[h]`.

Simplify using `[h, Ne.symm h]`. Establish `hc : LinearIndependent E c` using `Fintype.linearIndependent_iff.2 fun g hg j => by`. Use `congrArg (V.hT (d j)) hg` as an intermediate fact. Simplify `this` using `[map_sum, hdc]`. Take `⟨V', ι, hr, hι, h0⟩` from `GlobalTheory.WittLow.exists_lower hst V c hc hcc`.

Establish `h0' : ∀ x a, V.hT (c a) (ι x) = 0` using `fun x a => by rw [← hs.eq (ι x) (c a), h0, map_zero]`. Set `p : V.V →ₗ[E] V.V` to `LinearMap.id - ∑ k, (V.hT (d k)).smulRight (c k)`. Establish `hp : ∀ v, p v = v - ∑ k, V.hT (d k) v • c k` using `fun v => by simp [p, LinearMap.sum_apply]`. Establish `hcp : ∀ a v, V.hT (c a) (p v) = V.hT (c a) v` using `fun a v => by simp [hp, map_sum, hcc]`. Establish `hdp : ∀ a v, V.hT (d a) (p v) = 0` using `fun a v => by simp [hp, map_sum, hdc]`.

Establish `hiso : HSpace.IsIsomEmb V' V (p ∘ₗ ι)` using `fun x y => by`. Rewrite using `[← hι x y]`. Use `show V.hT (p (ι x)) (p (ι y)) = V.hT (ι x) (ι y)`. Establish `e1 : V.hT (ι x) (p (ι y)) = V.hT (ι x) (ι y)` using `by simp [hp, map_sum, h0]`. Rewrite using `[hp (ι x), map_sub, LinearMap.sub_apply, e1, map_sum, LinearMap.sum_apply]`.

Simplify using `[hcp, h0']`. Establish `hinj : Function.Injective ι` using `(injective_iff_map_eq_zero ι).2 fun x hx => V'.nondeg.1 x fun y => by rw [← hι x y, hx]; simp`. Use `set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (c j)) with hP`. Establish `hdisj : Disjoint (LinearMap.range ι) (Submodule.span E (Set.range c))`. Rewrite using `[Submodule.disjoint_def]`.

Introduce and unpack `_ ⟨x, rfl⟩ hx`. Take `⟨g, hg⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hx`. Establish `: x = 0` using `V'.nondeg.1 x fun y => by`. Rewrite using `[← hι x y, ← hg]`. Simplify using `[map_sum, LinearMap.sum_apply, h0']`.

Rewrite using `[this, map_zero]`. Establish `hle : LinearMap.range ι ⊔ Submodule.span E (Set.range c) ≤ P` using `sup_le (by rintro _ ⟨x, rfl⟩; exact funext fun j => h0' x j) (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact funext fun a => hcc a j))`. Establish `heq : LinearMap.range ι ⊔ Submodule.span E (Set.range c) = P`. Use `Submodule.eq_of_le_of_finrank_eq hle ?_` and prove the remaining obligations. Establish `e1` using `Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) (Submodule.span E (Set.range c))`.

Rewrite `e1` using `[hdisj.eq_bot, finrank_bot, LinearMap.finrank_range_of_inj hinj, finrank_span_eq_card hc, Fintype.card_fin]`. Establish `e2` using `GlobalTheory.WittLow.finrank_orth hs V.nondeg c hc`. Apply the tactic sequence `have e3 : Module.finrank E V'.V = V'.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V'.frame`. Apply the tactic sequence `have e4 : Module.finrank E V.V = V.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V.frame`. Rewrite `e2` using `[← hP]`.

Use linear arithmetic over natural numbers and integers. Use `⟨V', p ∘ₗ ι, hiso, fun v => ⟨?_, fun hv => ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨x, rfl⟩ i`. Conclude with `⟨(hcp i _).trans (h0' x i), hdp i _⟩`. Establish `hvP : v ∈ P` using `funext fun j => (hv j).1`.

Rewrite `hvP` using `[← heq]`. Take `⟨_, ⟨x, rfl⟩, u, hu, rfl⟩` from `Submodule.mem_sup.1 hvP`. Take `⟨g, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hu`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hg : ∀ k, V.hT (d k) (ι x) = -g k` using `fun k => by`.

Use `(hv k).2` as an intermediate fact. Simplify using `[map_sum, hdc] at this`. Conclude with `eq_neg_of_add_eq_zero_left this`. Use `show p (ι x) = _`. Simplify using `[hp, hg, sub_eq_add_neg]`.
-/
theorem exists_perp {E : Type} [Field E] [NumberField E] [StarRing E] (hst : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (V : HSpace E) {n : ℕ} (c d : Fin n → V.V) (hcc : ∀ i j, V.hT (c i) (c j) = 0)
    (hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0) :
    ∃ (V' : HSpace E) (ι : V'.V →ₗ[E] V.V), HSpace.IsIsomEmb V' V ι ∧
      ∀ v, v ∈ LinearMap.range ι ↔ ∀ i, V.hT (c i) v = 0 ∧ V.hT (d i) v = 0 := by
  classical
  have hs := V.herm
  have hdc : ∀ i j, V.hT (d i) (c j) = if i = j then 1 else 0 := fun i j => by
    rw [← hs.eq (c j) (d i), hcd]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  have hc : LinearIndependent E c := Fintype.linearIndependent_iff.2 fun g hg j => by
    have := congrArg (V.hT (d j)) hg
    simpa [map_sum, hdc] using this
  obtain ⟨V', ι, hr, hι, h0⟩ := GlobalTheory.WittLow.exists_lower hst V c hc hcc
  have h0' : ∀ x a, V.hT (c a) (ι x) = 0 := fun x a => by rw [← hs.eq (ι x) (c a), h0, map_zero]
  let p : V.V →ₗ[E] V.V := LinearMap.id - ∑ k, (V.hT (d k)).smulRight (c k)
  have hp : ∀ v, p v = v - ∑ k, V.hT (d k) v • c k := fun v => by simp [p, LinearMap.sum_apply]
  have hcp : ∀ a v, V.hT (c a) (p v) = V.hT (c a) v := fun a v => by simp [hp, map_sum, hcc]
  have hdp : ∀ a v, V.hT (d a) (p v) = 0 := fun a v => by simp [hp, map_sum, hdc]
  have hiso : HSpace.IsIsomEmb V' V (p ∘ₗ ι) := fun x y => by
    rw [← hι x y]
    show V.hT (p (ι x)) (p (ι y)) = V.hT (ι x) (ι y)
    have e1 : V.hT (ι x) (p (ι y)) = V.hT (ι x) (ι y) := by simp [hp, map_sum, h0]
    rw [hp (ι x), map_sub, LinearMap.sub_apply, e1, map_sum, LinearMap.sum_apply]
    simp [hcp, h0']
  have hinj : Function.Injective ι := (injective_iff_map_eq_zero ι).2 fun x hx =>
    V'.nondeg.1 x fun y => by rw [← hι x y, hx]; simp
  set P : Submodule E V.V := LinearMap.ker (LinearMap.pi fun j => V.hT (c j)) with hP
  have hdisj : Disjoint (LinearMap.range ι) (Submodule.span E (Set.range c)) := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hx
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have : x = 0 := V'.nondeg.1 x fun y => by
      rw [← hι x y, ← hg]
      simp [map_sum, LinearMap.sum_apply, h0']
    rw [this, map_zero]
  have hle : LinearMap.range ι ⊔ Submodule.span E (Set.range c) ≤ P :=
    sup_le (by rintro _ ⟨x, rfl⟩; exact funext fun j => h0' x j)
      (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact funext fun a => hcc a j))
  have heq : LinearMap.range ι ⊔ Submodule.span E (Set.range c) = P := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    have e1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ι) (Submodule.span E (Set.range c))
    rw [hdisj.eq_bot, finrank_bot, LinearMap.finrank_range_of_inj hinj, finrank_span_eq_card hc, Fintype.card_fin] at e1
    have e2 := GlobalTheory.WittLow.finrank_orth hs V.nondeg c hc
    have e3 : Module.finrank E V'.V = V'.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V'.frame
    have e4 : Module.finrank E V.V = V.rank := by first | rfl | simpa using Module.finrank_eq_card_basis V.frame
    rw [← hP] at e2
    omega
  refine ⟨V', p ∘ₗ ι, hiso, fun v => ⟨?_, fun hv => ?_⟩⟩
  · rintro ⟨x, rfl⟩ i
    exact ⟨(hcp i _).trans (h0' x i), hdp i _⟩
  · have hvP : v ∈ P := funext fun j => (hv j).1
    rw [← heq] at hvP
    obtain ⟨_, ⟨x, rfl⟩, u, hu, rfl⟩ := Submodule.mem_sup.1 hvP
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hu
    refine ⟨x, ?_⟩
    have hg : ∀ k, V.hT (d k) (ι x) = -g k := fun k => by
      have := (hv k).2
      simp [map_sum, hdc] at this
      exact eq_neg_of_add_eq_zero_left this
    show p (ι x) = _
    simp [hp, hg, sub_eq_add_neg]

/- English proof (translation)
Introduce `D V m X Y h T`. Set `e` to `Fintype.equivFin {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}`. Set `c : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V` to `fun k => V.frame.equivFun.symm fun j => X j (e.symm k).1`. Set `d : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V` to `fun k => V.frame.equivFun.symm fun j => Y j (e.symm k).1`. Establish `hcc : ∀ i j, V.hT (c i) (c j) = 0` using `fun i j => by`.

Simplify using `only [c]`. Rewrite using `[hT_cols, h.xx]`. Both sides reduce to the same expression. Establish `hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0` using `fun i j => by`. Simplify using `only [c, d]`.

Rewrite using `[hT_cols, h.xy, Matrix.one_apply]`. Simplify using `only [Subtype.val_inj, e.symm.apply_eq_iff_eq]`. Take `⟨V', ι, hι, hr⟩` from `exists_perp Formalism.BasicNotions.Examples₂.star_isIntegral V c d hcc hcd`. Use `⟨V', ι, hι, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`.

Prove the components needed by the constructor for the conclusion. Introduce `hv i hi`. Use `hv (e ⟨i, hi⟩)` as an intermediate fact. Simplify `this` using `[c, d]`. Introduce `hv k`.

Conclude with `hv _ (e.symm k).2`.
-/
theorem exists_compl : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), ∃ (V' : HSp D) (ι : V'.V →ₗ[D.host.E] V.V), HSpace.IsIsomEmb V' V ι ∧ ∀ v : V.V, v ∈ LinearMap.range ι ↔ ∀ i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T, V.hT (V.frame.equivFun.symm fun j => X j i) v = 0 ∧ V.hT (V.frame.equivFun.symm fun j => Y j i) v = 0 := by
  intro D V m X Y h T
  classical
  let e := Fintype.equivFin {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}
  let c : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => X j (e.symm k).1
  let d : Fin (Fintype.card {i // i ∈ GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.upTo T}) → V.V :=
    fun k => V.frame.equivFun.symm fun j => Y j (e.symm k).1
  have hcc : ∀ i j, V.hT (c i) (c j) = 0 := fun i j => by
    simp only [c]
    rw [hT_cols, h.xx]
    rfl
  have hcd : ∀ i j, V.hT (c i) (d j) = if i = j then 1 else 0 := fun i j => by
    simp only [c, d]
    rw [hT_cols, h.xy, Matrix.one_apply]
    simp only [Subtype.val_inj, e.symm.apply_eq_iff_eq]
  obtain ⟨V', ι, hι, hr⟩ := exists_perp Formalism.BasicNotions.Examples₂.star_isIntegral V c d hcc hcd
  refine ⟨V', ι, hι, fun v => ?_⟩
  rw [hr]
  constructor
  · intro hv i hi
    have := hv (e ⟨i, hi⟩)
    simpa [c, d] using this
  · intro hv k
    exact hv _ (e.symm k).2

end GlobalTheory.CompanionTheory.WittCompl

end
