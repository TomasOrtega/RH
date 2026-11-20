import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordApply

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.WachTie

open PowerSeries in

/- English proof (translation)
Introduce `G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W T r hu ⟨b⟩`. Establish `hmul : ∀ g ∈ W.DelF, ∀ δ ∈ W.DelF, g * δ ∈ W.DelF`. Introduce `g hg δ hδ`. Take `⟨a, ha, hga⟩` from `(W.DelF_def g).1 hg`. Take `⟨c, hc, hδc⟩` from `(W.DelF_def δ).1 hδ`.

Use `(W.DelF_def _).2 ⟨a * c, Nat.mul_pos ha hc, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_mul, hga, one_pow, one_mul, mul_comm, pow_mul, hδc, one_pow]`. Establish `himage : ∀ g ∈ W.DelF, W.DelF.image (g * ·) = W.DelF`. Introduce `g hg`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises.

Introduce `x hx`. Take `⟨δ, hδ, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `hmul g hg δ hδ`. Rewrite using `[Finset.card_image_of_injective _ (mul_right_injective g)]`. Set `avg : W.DD T →ₗ[O] W.DD T` to `((↑hu.unit⁻¹ : O)) • ∑ δ ∈ W.DelF, W.γD T δ`.

Establish `havg : ∀ x, avg x = (↑hu.unit⁻¹ : O) • ∑ δ ∈ W.DelF, W.γD T δ x`. Introduce `x`. Simplify using `[avg, LinearMap.sum_apply]`. Establish `hinv : ∀ g ∈ W.DelF, ∀ x, W.γD T g (avg x) = avg x`. Introduce `g hg x`.

Rewrite using `[havg, map_smul, map_sum]`. Use `congr 1`. Repeatedly rewrite using `[← W.γD_mul T]`. Use `conv_rhs => rw [← himage g hg]`. Rewrite using `[Finset.sum_image (fun a _ c _ h => mul_left_cancel h)]`.

Establish `hN : ∀ x ∈ W.N T, avg x ∈ W.N T`. Introduce `x hx`. Rewrite using `[havg]`. Conclude with `Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => W.N_Γ T δ x hx)`. Use `open Pointwise in`.

Establish `hQ : ∀ x ∈ W.N T, avg x - x ∈ (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • W.N T`. Introduce `x hx`. Establish `hsplit : avg x - x = (↑hu.unit⁻¹ : O) • ∑ δ ∈ W.DelF, (W.γD T δ x - x)`. Rewrite using `[havg, Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul O, smul_smul, IsUnit.val_inv_mul, one_smul]`. Rewrite using `[hsplit]`.

Use `Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => ?_)` and prove the remaining obligations. Take `⟨y, hy, hxy⟩` from `W.N_π T δ x hx`. Rewrite using `[hxy]`. Conclude with `Submodule.smul_mem_pointwise_smul _ _ _ hy`. Establish `hb : ∀ k, ∃ y : W.N T, (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • y = (⟨avg (b k), hN _ (b k).2⟩ : W.N T) - b k`.

Introduce `k`. Use `open Pointwise in`. Take `⟨y, hy, hxy⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hQ _ (b k).2)`. Conclude with `⟨⟨y, hy⟩, Subtype.ext (by simpa using hxy)⟩`. Use `choose y hy using hb`.

Set `g : W.N T →ₗ[_root_.Formalism.BasicNotions.LetA O n] W.N T` to `b.constr (_root_.Formalism.BasicNotions.LetA O n) y`. Set `f : W.N T →ₗ[_root_.Formalism.BasicNotions.LetA O n] W.N T` to `LinearMap.id + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • g`. Establish `hf : ∀ k, f (b k) = ⟨avg (b k), hN _ (b k).2⟩`. Introduce `k`. Simplify using `only [f, g, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, Module.Basis.constr_basis, hy]`.

Normalize the expressions using the abelian group laws. Establish `hunit : IsUnit f` using `by haveI := Module.Free.of_basis b haveI := Module.Finite.of_basis b`. Rewrite using `[LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix b]`. Establish `hM : LinearMap.toMatrix b b f = 1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g`. Simplify using `[f, map_add, LinearMap.toMatrix_id]`.

Rewrite using `[hM, Pi.isUnit_iff]`. Introduce `i`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`. Set `ψ : _root_.Formalism.BasicNotions.LetA O n →+* O` to `(PowerSeries.constantCoeff (R := O)).comp (Pi.evalRingHom (fun _ : ZMod n => O⟦X⟧) i)`. Express the relevant statement in the definitionally equal form `IsUnit (ψ (Matrix.det (1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g)))`.

Rewrite using `[RingHom.map_det]`. Establish `h2 : ψ.mapMatrix (1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g) = 1`. Use extensionality with `p q`. Simplify using `[ψ, _root_.Formalism.BasicNotions.letπ, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[h2, Matrix.det_one]`. Conclude with `isUnit_one`. Establish `hbij` using `(Module.End.isUnit_iff f).1 hunit`. Use `⟨b.map (LinearEquiv.ofBijective f hbij), fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[Module.Basis.map_apply, LinearEquiv.ofBijective_apply, hf]`.

Conclude with `⟨hN _ (b k).2, fun δ hδ => hinv δ hδ _⟩`.
-/
theorem _root_.GlobalTheory.WachTie.exists_invariant_basis : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) {r : ℕ}, IsUnit (W.DelF.card : O) → Nonempty (Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T)) → ∃ b : Module.Basis (Fin r) (_root_.Formalism.BasicNotions.LetA O n) ↥(W.N T), ∀ k, (b k : W.DD T) ∈ W.NΔ T := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W T r hu ⟨b⟩
  classical
  have hmul : ∀ g ∈ W.DelF, ∀ δ ∈ W.DelF, g * δ ∈ W.DelF := by
    intro g hg δ hδ
    obtain ⟨a, ha, hga⟩ := (W.DelF_def g).1 hg
    obtain ⟨c, hc, hδc⟩ := (W.DelF_def δ).1 hδ
    refine (W.DelF_def _).2 ⟨a * c, Nat.mul_pos ha hc, ?_⟩
    rw [mul_pow, pow_mul, hga, one_pow, one_mul, mul_comm, pow_mul, hδc, one_pow]
  have himage : ∀ g ∈ W.DelF, W.DelF.image (g * ·) = W.DelF := by
    intro g hg
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hx
      exact hmul g hg δ hδ
    · rw [Finset.card_image_of_injective _ (mul_right_injective g)]
  let avg : W.DD T →ₗ[O] W.DD T := ((↑hu.unit⁻¹ : O)) • ∑ δ ∈ W.DelF, W.γD T δ
  have havg : ∀ x, avg x = (↑hu.unit⁻¹ : O) • ∑ δ ∈ W.DelF, W.γD T δ x := by
    intro x
    simp [avg, LinearMap.sum_apply]
  have hinv : ∀ g ∈ W.DelF, ∀ x, W.γD T g (avg x) = avg x := by
    intro g hg x
    rw [havg, map_smul, map_sum]
    congr 1
    simp_rw [← W.γD_mul T]
    conv_rhs => rw [← himage g hg]
    rw [Finset.sum_image (fun a _ c _ h => mul_left_cancel h)]
  have hN : ∀ x ∈ W.N T, avg x ∈ W.N T := by
    intro x hx
    rw [havg]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => W.N_Γ T δ x hx)
  open Pointwise in
  have hQ : ∀ x ∈ W.N T, avg x - x ∈ (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • W.N T := by
    intro x hx
    have hsplit : avg x - x = (↑hu.unit⁻¹ : O) • ∑ δ ∈ W.DelF, (W.γD T δ x - x) := by
      rw [havg, Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul O,
        smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [hsplit]
    refine Submodule.smul_of_tower_mem _ _ (Submodule.sum_mem _ fun δ _ => ?_)
    obtain ⟨y, hy, hxy⟩ := W.N_π T δ x hx
    rw [hxy]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hy
  have hb : ∀ k, ∃ y : W.N T, (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • y =
      (⟨avg (b k), hN _ (b k).2⟩ : W.N T) - b k := by
    intro k
    open Pointwise in
    obtain ⟨y, hy, hxy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 (hQ _ (b k).2)
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hxy)⟩
  choose y hy using hb
  let g : W.N T →ₗ[_root_.Formalism.BasicNotions.LetA O n] W.N T := b.constr (_root_.Formalism.BasicNotions.LetA O n) y
  let f : W.N T →ₗ[_root_.Formalism.BasicNotions.LetA O n] W.N T := LinearMap.id + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • g
  have hf : ∀ k, f (b k) = ⟨avg (b k), hN _ (b k).2⟩ := by
    intro k
    simp only [f, g, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply,
      Module.Basis.constr_basis, hy]
    abel
  have hunit : IsUnit f := by
    haveI := Module.Free.of_basis b
    haveI := Module.Finite.of_basis b
    rw [LinearMap.isUnit_iff_isUnit_det, ← LinearMap.det_toMatrix b]
    have hM : LinearMap.toMatrix b b f = 1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g := by
      simp [f, map_add, LinearMap.toMatrix_id]
    rw [hM, Pi.isUnit_iff]
    intro i
    rw [PowerSeries.isUnit_iff_constantCoeff]
    let ψ : _root_.Formalism.BasicNotions.LetA O n →+* O :=
      (PowerSeries.constantCoeff (R := O)).comp (Pi.evalRingHom (fun _ : ZMod n => O⟦X⟧) i)
    change IsUnit (ψ (Matrix.det (1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g)))
    rw [RingHom.map_det]
    have h2 : ψ.mapMatrix (1 + (_root_.Formalism.BasicNotions.letπ : _root_.Formalism.BasicNotions.LetA O n) • LinearMap.toMatrix b b g) = 1 := by
      ext p q
      simp [ψ, _root_.Formalism.BasicNotions.letπ, Matrix.one_apply]
      split_ifs <;> simp
    rw [h2, Matrix.det_one]
    exact isUnit_one
  have hbij := (Module.End.isUnit_iff f).1 hunit
  refine ⟨b.map (LinearEquiv.ofBijective f hbij), fun k => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply, hf]
  exact ⟨hN _ (b k).2, fun δ hδ => hinv δ hδ _⟩

end GlobalTheory.WachTie
