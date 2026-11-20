import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

/- English proof (translation)
Establish `h` using `M.add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.mp h.symm`.
-/
private theorem pt_zero_lemma {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) : M.pt 0 = 1 := by
  have h := M.add 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro v`. Simplify using `[pt_zero_lemma M]`. Consider the case `succ n ih`.

Introduce `v`. Rewrite using `[Fin.sum_univ_succ, M.add, ih, List.ofFn_succ, List.prod_cons]`.
-/
private theorem LieModel_pt_sum_eq_prod {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) :
    ∀ (n : ℕ) (v : Fin n → U), M.pt (∑ k, v k) = (List.ofFn fun k => M.pt (v k)).prod := by
  intro n
  induction n with
  | zero => intro v; simp [pt_zero_lemma M]
  | succ n ih =>
    intro v
    rw [Fin.sum_univ_succ, M.add, ih, List.ofFn_succ, List.prod_cons]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.Ar.Fl.IsComb`. Rewrite using `[LieModel_pt_sum_eq_prod M]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Establish `hv' : v = fun i => M.pt (c i • u i)`.

Use function extensionality and compare the values at `i`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hv i, M.smul]`. Rewrite using `[hv']`. Introduce `h`.

Use `⟨fun i => M.pt (c i • u i), fun i => ?_, h⟩` and prove the remaining obligations. Rewrite using `[M.smul]`.
-/
private theorem isComb_pt_iff_eq_pt_sum {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) (n : ℕ) (c : Fin n → R) (u : Fin n → U)
    (w : epsAt x ⟶ G) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k) := by
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsComb
  rw [LieModel_pt_sum_eq_prod M]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : v = fun i => M.pt (c i • u i) := by
      funext i
      apply Over.OverMorphism.ext
      rw [hv i, M.smul]
    rw [hv']
  · intro h
    refine ⟨fun i => M.pt (c i • u i), fun i => ?_, h⟩
    rw [M.smul]

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec eigSp`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ a`. Apply `M.inj` to reduce the goal to its premises.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[hM a u, M.smul, h a]`. Introduce `h`. Use `⟨M.tan u, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← hM a u, h a, M.smul]`.
-/
private theorem isEigVec_pt_iff_mem_eigSp {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {U : Type} [AddCommGroup U] [Module R U] (M : LieModel G x U) {O : Type} [CommRing O] (act : OAct O G)
    (ρ : O →+* Module.End R U) (τ : O →+* R) (hM : M.IsActOf act.act ρ) (u : U) :
    GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ := by
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsEigVec eigSp
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  constructor
  · rintro ⟨-, h⟩ a
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hM a u, M.smul, h a]
  · intro h
    refine ⟨M.tan u, fun a => ?_⟩
    rw [← hM a u, h a, M.smul]

/- English proof (translation)
Introduce `S R _ G _ x U _ _ M`. Use `⟨fun n c u w => isComb_pt_iff_eq_pt_sum M n c u w, fun O _ act ρ τ hM => ⟨fun u => isEigVec_pt_iff_mem_eigSp M act ρ τ hM u, fun n u => ?_⟩⟩` and prove the remaining obligations. Unfold `GlobalTheory.CompanionTheory.Ar.Fl.IsEigFrame`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hu, huniq⟩`.

Establish `hu' : ∀ i, u i ∈ eigSp ρ τ` using `fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mp (hu i)`. Establish `hex : ∀ e ∈ eigSp ρ τ, ∃! c : Fin n → R, e = ∑ k, c k • u k`. Introduce `e he`. Take `⟨c, hc, huq⟩` from `huniq (M.pt e) ((isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mpr he)`. Conclude with `⟨c, M.inj ((isComb_pt_iff_eq_pt_sum M n c u _).mp hc), fun c' hc' => huq c' ((isComb_pt_iff_eq_pt_sum M n c' u _).mpr (congrArg M.pt hc'))⟩`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Take `⟨c, -, huq⟩` from `hex 0 (Submodule.zero_mem _)`. Establish `hg0 : g = 0` using `(huq g hg.symm).trans (huq 0 (by simp)).symm`.

Rewrite using `[hg0]`. Both sides reduce to the same expression. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Conclude with `hu' i`. Introduce `e he`. Take `⟨c, hc, -⟩` from `hex e he`. Rewrite using `[hc]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Introduce and unpack `⟨hli, hsp⟩`. Establish `hu' : ∀ i, u i ∈ eigSp ρ τ` using `fun i => hsp ▸ Submodule.subset_span ⟨i, rfl⟩`. Use `⟨fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mpr (hu' i), fun w hw => ?_⟩` and prove the remaining obligations. Establish `ht : IsTanAt G x w`. Take `⟨h, -⟩` from `hw`.

Conclude with `h`. Take `⟨e, rfl⟩` from `M.onto w ht`. Establish `he : e ∈ eigSp ρ τ` using `(isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mp hw`. Rewrite `he` using `[← hsp]`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp he`.

Use `⟨c, (isComb_pt_iff_eq_pt_sum M n c u _).mpr (congrArg M.pt hc.symm), fun c' hc' => ?_⟩` and prove the remaining obligations. Establish `h1 : e = ∑ k, c' k • u k` using `M.inj ((isComb_pt_iff_eq_pt_sum M n c' u _).mp hc')`. Establish `h2 : ∑ k, (c' k - c k) • u k = 0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[← h1, hc, sub_self]`.

Use function extensionality and compare the values at `k`. Conclude with `sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h2 k)`.
-/
theorem lie_model_eigenvectors_action : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (U : Type) [AddCommGroup U] [Module R U] (M : LieModel G x U), (∀ (n : ℕ) (c : Fin n → R) (u : Fin n → U) w, IsComb c (fun k => M.pt (u k)) w ↔ w = M.pt (∑ k, c k • u k)) ∧ ∀ (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End R U) (τ : O →+* R), M.IsActOf act.act ρ → (∀ u, IsEigVec act x τ (M.pt u) ↔ u ∈ eigSp ρ τ) ∧ ∀ (n : ℕ) (u : Fin n → U), IsEigFrame act x τ (fun k => M.pt (u k)) ↔ LinearIndependent R u ∧ Submodule.span R (Set.range u) = eigSp ρ τ := by
  intro S R _ G _ x U _ _ M
  refine ⟨fun n c u w => isComb_pt_iff_eq_pt_sum M n c u w, fun O _ act ρ τ hM => ⟨fun u => isEigVec_pt_iff_mem_eigSp M act ρ τ hM u, fun n u => ?_⟩⟩
  unfold GlobalTheory.CompanionTheory.Ar.Fl.IsEigFrame
  constructor
  · rintro ⟨hu, huniq⟩
    have hu' : ∀ i, u i ∈ eigSp ρ τ := fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mp (hu i)
    have hex : ∀ e ∈ eigSp ρ τ, ∃! c : Fin n → R, e = ∑ k, c k • u k := by
      intro e he
      obtain ⟨c, hc, huq⟩ := huniq (M.pt e) ((isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mpr he)
      exact ⟨c, M.inj ((isComb_pt_iff_eq_pt_sum M n c u _).mp hc),
        fun c' hc' => huq c' ((isComb_pt_iff_eq_pt_sum M n c' u _).mpr (congrArg M.pt hc'))⟩
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain ⟨c, -, huq⟩ := hex 0 (Submodule.zero_mem _)
      have hg0 : g = 0 := (huq g hg.symm).trans (huq 0 (by simp)).symm
      rw [hg0]
      rfl
    · apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hu' i
      · intro e he
        obtain ⟨c, hc, -⟩ := hex e he
        rw [hc]
        exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro ⟨hli, hsp⟩
    have hu' : ∀ i, u i ∈ eigSp ρ τ := fun i => hsp ▸ Submodule.subset_span ⟨i, rfl⟩
    refine ⟨fun i => (isEigVec_pt_iff_mem_eigSp M act ρ τ hM (u i)).mpr (hu' i), fun w hw => ?_⟩
    have ht : IsTanAt G x w := by
      obtain ⟨h, -⟩ := hw
      exact h
    obtain ⟨e, rfl⟩ := M.onto w ht
    have he : e ∈ eigSp ρ τ := (isEigVec_pt_iff_mem_eigSp M act ρ τ hM e).mp hw
    rw [← hsp] at he
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp he
    refine ⟨c, (isComb_pt_iff_eq_pt_sum M n c u _).mpr (congrArg M.pt hc.symm), fun c' hc' => ?_⟩
    have h1 : e = ∑ k, c' k • u k := M.inj ((isComb_pt_iff_eq_pt_sum M n c' u _).mp hc')
    have h2 : ∑ k, (c' k - c k) • u k = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← h1, hc, sub_self]
    funext k
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h2 k)

end PositivityTheory.Xgf
